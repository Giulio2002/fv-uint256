#!/usr/bin/env python3
"""scripts/upgrade-witness-run.py [--check] [--dry] FILE...   (rule U-WITNESS-RUN, Janus agent/up3-vacuity)

Rewrites every witness theorem (`theorem <name> : ∃ ...` inside a `Witness` namespace, see witness-theorems.py) of FILE to the
returning-run shape: the statement gets a last conjunct
    Returns (<program of CallSetup>) s fun s' => ABIReturn s s' ∧ <post s s'>      (EnsuresGo: GoReturns ... match)
and the proof gets, as its last component, `correctness <vars> <hyp proofs> ret hret s setup <pre proof>`: the main theorem itself
supplies the run.  The existing proof components are kept: the proof must be an anonymous constructor
    ⟨<values of the ∃ variables>, <proof of each hypothesis conjunct>, <hret>, <setup>, <proof of each pre conjunct>⟩.
Every component that is not a plain identifier becomes a named hole `?wK` (filled by `case wK => exact ...`), so it is elaborated once
and shared by the conjunct and the correctness application.

Idempotent: a witness whose statement already has a `Returns`/`GoReturns` conjunct is left alone.  A witness the script cannot
handle is reported as MANUAL <file> <theorem> <reason> and not touched.

Extension point (U-WITNESS-CALLSITE, not frozen): EXTRA_CONJUNCTS below is called per witness with the parsed context and may add
conjunct texts (and proof components) after the Returns conjunct.
"""
import re, sys

def strip_comments(src):
    # blank out comments and string literals, preserving offsets
    out = list(src); i = 0; n = len(src)
    while i < n:
        c = src[i]
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            for k in range(i, j): out[k] = ' '
            i = j
        elif src.startswith('/-', i):
            depth = 1; j = i + 2
            while j < n and depth:
                if src.startswith('/-', j): depth += 1; j += 2
                elif src.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            for k in range(i, j):
                if out[k] != '\n': out[k] = ' '
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != '\n': out[k] = ' '
            i = j + 1
        elif c == "'" and i + 2 < n and src[i + 2] == "'" and src[i+1] != '\\':
            out[i + 1] = ' '; i += 3
        else:
            i += 1
    return ''.join(out)

OPEN = '([{⟨'; CLOSE = ')]}⟩'

def split_top(text, seps):
    """split text at depth-0 occurrences of any string in seps (longest first); returns list of (piece)"""
    seps = sorted(seps, key=len, reverse=True)
    out = []; depth = 0; cur = 0; i = 0; n = len(text)
    while i < n:
        c = text[i]
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        elif depth == 0:
            for sp in seps:
                if text.startswith(sp, i):
                    out.append(text[cur:i]); i += len(sp); cur = i; break
            else:
                i += 1; continue
            continue
        i += 1
    out.append(text[cur:])
    return out

def find_top(text, tok, start=0):
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        elif depth == 0 and text.startswith(tok, i): return i
    return -1

def atoms(text):
    """whitespace-separated atoms at depth 0"""
    out = []; depth = 0; cur = []
    for c in text:
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        if depth == 0 and c.isspace():
            if cur: out.append(''.join(cur)); cur = []
        else: cur.append(c)
    if cur: out.append(''.join(cur))
    return out

def decls(src):
    """(ns, kind, name, start, end) for each declaration-ish line; ns = namespace stack"""
    ms = list(re.finditer(r'^(namespace\s+(\S+)|end\s+(\S+)|(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev|instance|macro|macro_rules|syntax|elab|open|section|set_option|attribute|variable|example|structure|inductive|class|notation|local|scoped|initialize|opaque|axiom|@\[)\b[^\n]*)', src, re.M))
    ns = []; out = []
    for k, m in enumerate(ms):
        if m.group(2):
            for part in m.group(2).split('.'): pass
            ns.append(m.group(2)); continue
        if m.group(3):
            if ns and ns[-1] == m.group(3): ns.pop()
            continue
        mm = re.match(r'(?:private\s+|protected\s+)*(theorem|lemma)\s+(\S+)', m.group(0))
        end = ms[k + 1].start() if k + 1 < len(ms) else len(src)
        if mm: out.append((list(ns), mm.group(1), mm.group(2), m.start(), end))
    return out

def top_assign(text, start=0):
    """index of the first `:=` at depth 0 at/after start"""
    return find_top(text, ':=', start)

def parse_binders(s):
    """explicit binder groups of a binder-list text: list of (kind, names, type)"""
    out = []; i = 0; n = len(s)
    while i < n:
        c = s[i]
        if c in '({[⦃':
            close = {'(': ')', '{': '}', '[': ']', '⦃': '⦄'}[c]
            depth = 0; j = i
            while j < n:
                if s[j] in '([{⟨⦃': depth += 1
                elif s[j] in ')]}⟩⦄': depth -= 1
                if depth == 0: break
                j += 1
            inner = s[i + 1:j]
            if c == '[': out.append(('inst', [], inner))
            else:
                k = find_top(inner, ':')
                names = inner[:k].split(); ty = inner[k + 1:].strip()
                out.append(('explicit' if c == '(' else 'implicit', names, ty))
            i = j + 1
        else: i += 1
    return out

class Manual(Exception): pass

# values of main-theorem binders that the witness statement replaces by a literal (and that no CallSetup argument shows):
# {module file stem: {binder name: Lean term}}
# keys: 'Stem', 'Stem/isa', 'Stem/isa/witnessName'
HINTS = {
    'CmpBig': {'len': '2'}, 'SetFromBig': {'len': '2'},
    'Format/arm64': {'fW': 'fa', 'fP': 'fa', 'fF': 'fa', 'fWr': 'fa', 'stack': '4608', 'b0': '0x400', 'zv': '16',
                     'RW': 'Rc', 'RP': 'Rc', 'RF': 'Rc', 'RWr': 'Rc', 'RFp': 'Rd', 'RBf': 'Rd'},
    'Format/arm64/nil': {'zv': '0'},
    'Format/amd64': {'fW': '7340032', 'fP': '7340032', 'fF': '7340032', 'fWr': '7340032', 'stack': '4608', 'b0': '1024', 'zv': '16'},
    'Format/amd64/nil': {'zv': '0'},
}

# Extension point (U-WITNESS-CALLSITE): returns a list of extra conjunct texts to append after the Returns conjunct.
def EXTRA_CONJUNCTS(ctx): return []


def parse_main(src, cs, d):
    ns, kind, name, st, en = d
    t = cs[st:en]
    a = top_assign(t)
    if a < 0: raise Manual('main: no :=')
    head = t[:a]
    m = re.match(r'\s*(?:private\s+)?(?:theorem|lemma)\s+\S+', head)
    rest = head[m.end():]
    # binders up to the first depth-0 ':' that is not ':='
    k = 0; depth = 0; colon = -1
    while k < len(rest):
        c = rest[k]
        if c in OPEN: depth += 1
        elif c in CLOSE: depth -= 1
        elif depth == 0 and c == ':' and not rest.startswith(':=', k): colon = k; break
        k += 1
    if colon < 0: raise Manual('main: no colon')
    binders = parse_binders(rest[:colon])
    stmt = rest[colon + 1:]
    parts = [p.strip() for p in split_top(stmt, ['→'])]
    concl = parts[-1]; prem = parts[:-1]
    at = atoms(concl)
    if at[0] not in ('Ensures', 'EnsuresGo'): raise Manual('main: conclusion is ' + at[0])
    return dict(binders=binders, prem=prem, concl_atoms=at, kind=at[0])

def subst_names(body, mapping):
    for a, b in mapping.items():
        if a != b: body = re.sub(r"(?<![\w'.])" + re.escape(a) + r"(?![\w'])", b, body)
    return body

def lam(atom, nparams):
    """(fun a b => body) -> (params, body) or None"""
    t = atom.strip()
    if t.startswith('(') and t.endswith(')'):
        inner = t[1:-1].strip()
        m = re.match(r'fun\s+((?:[\w\'_]+\s+){%d})=>\s*(.*)$' % nparams, inner, re.S)
        if m and split_depth0_ok(inner): return m.group(1).split(), m.group(2).strip()
    return None

def split_depth0_ok(t):
    d = 0
    for c in t:
        if c in OPEN: d += 1
        elif c in CLOSE:
            d -= 1
            if d < 0: return False
    return d == 0

def needs_paren(body):
    return find_top(body, '∨') >= 0 or find_top(body, '↔') >= 0 or find_top(body, '→') >= 0

def returns_conjunct(main, prog, s, ren):
    at = main['concl_atoms']
    # Ensures PROG ENTRY ARGS PRE POST ; EnsuresGo PROG ENTRY ARGS PRE C RET PAN
    sp = "s'"
    def app(atom, params, actual):
        r = lam(atom, len(params))
        if r:
            ps, body = r
            body = subst_names(body, {**{k: v for k, v in ren.items() if k not in ps}, **dict(zip(ps, actual))})
            return body
        return subst_names(atom, ren) + ' ' + ' '.join(actual)
    if main['kind'] == 'Ensures':
        post = at[5]
        body = app(post, ['s', 's2'], [s, sp])
        if needs_paren(body): body = '(' + body + ')'
        return f"Returns {prog} {s} fun {sp} => ABIReturn {s} {sp} ∧ {body}"
    else:
        C, rt, pan = at[5], at[6], at[7]
        C = subst_names(C, ren)
        if not lam(C, 1): c = '(' + C + ' ' + s + ')' if not re.match(r'^[\w.\']+$', C) else C + ' ' + s
        else: c = '(' + app(C, ['s'], [s]) + ')'
        r = app(rt, ['s', 's2'], [s, sp]); p = app(pan, ['s', 'v', 's2'], [s, 'v', sp])
        if needs_paren(r): r = '(' + r + ')'
        return (f"GoReturns {prog} {c} {s} fun o =>\n      match o with\n      | .returned {sp} => ABIReturn {s} {sp} ∧ {r}\n"
                f"      | .panicked v {sp} => {p}\n      | .goexited _ => False")

def is_group(item):
    t = item.strip()
    if not (t.startswith('(') and t.endswith(')')): return False
    d = 0
    for k, c in enumerate(t):
        if c in OPEN: d += 1
        elif c in CLOSE:
            d -= 1
            if d == 0 and k != len(t) - 1: return False
    return len(split_top(t[1:-1], ['∧'])) > 1

def group_items(item): return [x.strip() for x in split_top(item.strip()[1:-1], ['∧'])]

def upgrade(src, path, log):
    cs = strip_comments(src)
    ds = decls(cs)
    mains = {}
    for d in ds:
        if d[2] == 'correctness': mains['.'.join(d[0])] = d
    edits = []
    for d in ds:
        ns, kind, name, st, en = d
        if not any('Witness' in x for x in ns): continue
        t = cs[st:en]
        a = top_assign(t)
        hdr = t[:a] if a >= 0 else t
        m = re.match(r'\s*(?:private\s+)?(?:theorem|lemma)\s+\S+', hdr)
        stm = hdr[m.end():]
        if not re.match(r'\s*:\s*∃', stm): continue
        full = '.'.join(ns + [name])
        try:
            if re.search(r'(?<![\w.])(Returns|GoReturns)\b', stm):
                log('SKIP(already)', path, full); continue
            if a < 0: raise Manual('no :=')
            cand = None
            nsl = list(ns)
            while nsl and 'Witness' in nsl[-1]: nsl.pop()
            while True:
                key = '.'.join(nsl)
                if key in mains: cand = mains[key]; break
                if not nsl: break
                nsl.pop()
            if cand is None: raise Manual('no main theorem')
            main = parse_main(src, cs, cand)
            body_txt = stm.strip()[1:].strip()
            kc = find_top(body_txt, ',')
            binders_txt = body_txt[1:kc]
            if not binders_txt.strip().startswith('('): raise Manual('witness: bare ∃ binder')
            vars_ = []
            for kind_, names, ty in parse_binders(binders_txt):
                if kind_ != 'explicit': raise Manual('witness: non-explicit ∃ binder')
                vars_ += names
            items = [c.strip() for c in split_top(body_txt[kc + 1:].strip(), ['∧'])]
            def head(c): return c.lstrip('( ').split()[0] if c.strip() else ''
            def find(h): return next((i for i, c in enumerate(items) if head(c) == h), None)
            while find('RetAddr') is None and is_group(items[-1]): items = items[:-1] + group_items(items[-1])
            iret, isetup = find('RetAddr'), find('CallSetup')
            if iret is None or isetup is None or isetup != iret + 1: raise Manual('witness: no RetAddr/CallSetup conjuncts in order')
            # hypotheses = leaves of the items before RetAddr (groups are flattened)
            def leaves(item): return [l for x in group_items(item) for l in leaves(x)] if is_group(item) else [item]
            hyp_leaves = [l for it in items[:iret] for l in leaves(it)]
            # pin conjuncts (`def pinT ... : Prop := True`, brief rule: pins only in the witness) are not hypotheses of the main theorem
            is_pin = [bool(re.match(r'^(?:[\w.]*\.)?pin\w*$', head(l))) for l in hyp_leaves]
            nhyp = len(hyp_leaves) - sum(is_pin)
            cat = atoms(items[isetup])
            prog, entry, args, s = cat[1], cat[2], cat[3], cat[4]
            mret = re.match(r'\(?.*\.withExit\s+(\w+)\)?$', prog)
            retv = mret.group(1) if mret else None
            if retv is None: raise Manual('witness: cannot read ret from CallSetup')
            # main's precondition: number of conjuncts
            pre_atom = main['concl_atoms'][4]
            lm = lam(pre_atom, 1)
            kpre = len(split_top(lm[1], ['∧'])) if lm else 1
            holes = []; prelude = None
            proof_cs = cs[st:en][a + 2:]
            ps = proof_cs.strip()
            if re.match(r"^[\w.']+$", ps):
                # ---- core mode: the proof is a theorem stating the same existential: take it apart ----
                core = ps
                vals = {v: v for v in vars_}
                names = []; cnt = [0]
                def nm(prefix):
                    cnt[0] += 1; return f'{prefix}{cnt[0]}'
                def pat(item, destructure):
                    if destructure and is_group(item): return '⟨' + ', '.join(pat(x, True) for x in group_items(item)) + '⟩'
                    n = nm('h'); names.append((item, n)); return n
                parts = []; hyp_refs = []
                for i, it in enumerate(items):
                    if i < iret:
                        before = len(names); parts.append(pat(it, True)); hyp_refs += [n for l_, n in names[before:] if not re.match(r'^(?:[\w.]*\.)?pin\w*$', head(l_))]
                    elif i == iret: parts.append('hret'); hret_ref = 'hret'
                    elif i == isetup: parts.append('hsetup'); setup_ref = 'hsetup'
                    else:
                        n = nm('hp'); parts.append(n); names.append((it, n))
                pre_refs = [n for it, n in names if n.startswith('hp')]
                vl = ', '.join(vars_)
                pattern = f'⟨{vl}, {", ".join(parts)}⟩'
                rebuilt = ', '.join(parts)
                prelude = f'  obtain {pattern} := {core}'
                tail_term = rebuilt
                vlist = vl
                comp_refs = rebuilt
            else:
                if not ps.startswith('⟨'): raise Manual('proof is not an anonymous constructor: ' + ps[:40].replace('\n', ' '))
                proof = src[st:en][a + 2:]
                off = len(proof_cs) - len(proof_cs.lstrip())
                raw = proof[off:]
                depth = 0; endi = None
                for i, c in enumerate(proof_cs[off:]):
                    if c in OPEN: depth += 1
                    elif c in CLOSE:
                        depth -= 1
                        if depth == 0: endi = i; break
                if endi is None: raise Manual('unbalanced proof')
                tail = proof_cs[off + endi + 1:].strip()
                if tail: raise Manual('trailing text after proof: ' + tail[:40])
                inner_raw = raw[1:endi]; inner_cs = proof_cs[off + 1:off + endi]
                pieces = []; depth = 0; cur = 0
                for i, c in enumerate(inner_cs):
                    if c in OPEN: depth += 1
                    elif c in CLOSE: depth -= 1
                    elif c == ',' and depth == 0: pieces.append(inner_raw[cur:i].strip()); cur = i + 1
                pieces.append(inner_raw[cur:].strip())
                nv = len(vars_)
                if len(pieces) < nv + len(items): raise Manual(f'proof has {len(pieces)} components, expected >= {nv + len(items)}')
                if any(is_group(it) for it in items[:iret]): raise Manual('hypothesis groups in anonymous-constructor mode')
                vals = dict(zip(vars_, pieces[:nv]))
                comps = pieces[nv:]
                if len(comps) > len(items):
                    comps = comps[:len(items) - 1] + ['⟨' + ', '.join(comps[len(items) - 1:]) + '⟩']
                def ref(i, c):
                    if re.match(r"^[\w.']+$", c): return c
                    holes.append((f'w{i}', c)); return f'?w{i}'
                refs = [ref(i, c) for i, c in enumerate(comps)]
                hyp_refs = [r_ for r_, p_ in zip(refs[:len(hyp_leaves)], is_pin) if not p_]; hret_ref = refs[iret]; setup_ref = refs[isetup]
                pre_refs = refs[isetup + 1:]
                vlist = ', '.join(pieces[:nv]); comp_refs = ', '.join(refs)
            # pins in the precondition part (witness-only `pinBitVec64 x` conjuncts, alone or leading a group) are not part of main's pre
            is_pin_leaf = lambda l: bool(re.match(r'^(?:[\w.]*\.)?pin\w*$', head(l)))
            items_post = items[isetup + 1:]
            adj = []
            # witness-only conjuncts after correctness's precondition (e.g. `100 ≤ val`) must not enter the pre argument:
            # cut after the first item boundary where the (flat or top-level) conjunct count reaches kpre; no such boundary = no cut
            cut_ = None; cf_ = ct_ = 0; kept_ = 0
            for i_, it_ in enumerate(items_post):
                if not is_group(it_) and is_pin_leaf(it_): continue
                lv_ = [l_ for l_ in leaves(it_) if not is_pin_leaf(l_)]
                cf_ += len(lv_)
                ct_ += len([x_ for x_ in group_items(it_) if not is_pin_leaf(x_)]) if is_group(it_) else 1
                if cf_ == kpre or ct_ == kpre: cut_ = i_ + 1; break
            for i_, (it_, r_) in enumerate(zip(items_post, pre_refs)):
                if cut_ is not None and i_ >= cut_: break
                if not is_group(it_) and is_pin_leaf(it_): continue
                if is_group(it_):
                    k_ = 0
                    for l_ in leaves(it_):
                        if is_pin_leaf(l_): k_ += 1
                        else: break
                    if k_: r_ = '(' + r_ + ')' + '.2' * k_
                adj.append(r_)
            if len(items_post) == len(pre_refs): pre_refs = adj
            if cut_ is None and len(pre_refs) > kpre: pre_refs = pre_refs[:kpre]
            pre_arg = None if not pre_refs else (pre_refs[0] if len(pre_refs) == 1 else '⟨' + ', '.join(pre_refs) + '⟩')
            # ---- the call of the main theorem ----
            def val(v):
                x = vals[v]
                return x if re.match(r"^[\w.']+$", x) or (x.startswith('(') and x.endswith(')') and split_depth0_ok(x[1:-1])) else '(' + x + ')'
            call = []; hyp_i = 0
            ren = {}
            margs = [x.strip() for x in split_top(main['concl_atoms'][3].strip()[1:-1], [','])]
            wargs = [x.strip() for x in split_top(args.strip()[1:-1], [','])]
            if len(margs) != len(wargs): raise Manual('arg lists differ in length')
            for ma, wa in zip(margs, wargs):
                if re.match(r"^[\w']+$", ma) and ma != wa: ren[ma] = wa
            btype = {n_: ty_ for kk_, nn_, ty_ in main['binders'] for n_ in nn_}
            def lit(k, v):
                if re.match(r'^\d+$|^0x[0-9a-fA-F]+$', v):
                    return f'({v} : BitVec 64)' if 'BitVec' in btype.get(k, '') else (v if 'Nat' in btype.get(k, '') else f'({v})')
                return v if re.match(r"^[\w.']+$", v) else '(' + v + ')'
            ren_txt = {k: lit(k, v) for k, v in ren.items()}
            stem = re.sub(r'.*/', '', path)[:-5]
            isa_ = 'arm64' if '/Arm64/' in path else 'amd64'
            hints = {**HINTS.get(stem, {}), **HINTS.get(f'{stem}/{isa_}', {}), **HINTS.get(f'{stem}/{isa_}/{name}', {})}
            for k_, v_ in hints.items(): ren_txt[k_] = lit(k_, v_)
            # types of data binders: those of the witness's own ∃ variables, plus the usual ones
            data_types = {'Nat', 'BitVec', 'Int', 'List', 'Fin', 'Bool', 'Res', 'RtInv', 'IfaceModel', 'RtReady', 'PanicRuntime', 'Segment'}
            for kind_, names_, ty in parse_binders(binders_txt): data_types.add(re.sub(r'^.*?\.', '', atoms(ty)[0]) if atoms(ty) else '')
            def is_data(ty):
                at_ = atoms(ty.strip().lstrip('(') if False else ty)
                h_ = at_[0].lstrip('(') if at_ else ''
                return h_.split('.')[-1] in data_types
            for kind_, names_, ty in main['binders']:
                if kind_ == 'inst': raise Manual('main: instance binder')
                for n_ in names_:
                    if kind_ != 'explicit': continue
                    if ren.get(n_, n_) in vals: call.append(val(ren.get(n_, n_)))
                    elif n_ in ren: call.append(ren_txt[n_])
                    elif n_ in hints:
                        h = hints[n_]; call.append('(' + h + (' : BitVec 64' if re.match(r'^\d+$', h) and 'BitVec' in ty else '') + ')')
                    elif is_data(ty): call.append('_')
                    else:
                        if hyp_i >= nhyp: raise Manual(f'main binder {n_} is not a witness variable and no hypothesis conjunct is left')
                        call.append(hyp_refs[hyp_i]); hyp_i += 1
            for _ in main['prem']:
                if hyp_i >= nhyp: raise Manual('main has more hypotheses than the witness')
                call.append(hyp_refs[hyp_i]); hyp_i += 1
            if hyp_i != nhyp: raise Manual(f'witness has {nhyp} hypotheses, main {hyp_i}')
            if retv not in vals or s not in vals: raise Manual('ret/s are not witness variables')
            unresolved = [n_ for kind_, names_, ty in main['binders'] if kind_ == 'explicit' and is_data(ty) for n_ in names_
                          if ren.get(n_, n_) not in vals and n_ not in hints and n_ not in ren]
            body_main = ' '.join(main['concl_atoms'][5:])
            for n_ in unresolved:
                if re.search(r"(?<![\w'.])" + re.escape(n_) + r"(?![\w'])", body_main):
                    raise Manual(f'the postcondition mentions main binder {n_}, which the witness does not instantiate by a variable: add a HINTS entry')
            callterm = 'correctness ' + ' '.join(call + [val(retv), hret_ref, val(s), setup_ref] + ([pre_arg] if pre_arg else []))
            ret_conj = returns_conjunct(main, prog, s, ren_txt)
            raw_stm = src[st:en][m.end():a]
            new_stm = raw_stm.rstrip() + ' ∧\n    ' + ret_conj
            if prelude:
                new_proof = f"\n  by\n{prelude}\n  exact ⟨{vlist}, {comp_refs},\n    {callterm}⟩\n"
                new_proof = ' by\n' + prelude + f"\n  exact ⟨{vlist}, {comp_refs},\n    {callterm}⟩\n"
                tail_raw = src[st:en][a + 2:]
                tail_raw = tail_raw[len(tail_raw.rstrip()):]          # trailing whitespace after the proof
                end_of_proof = a + 2 + len(proof_cs.rstrip())
            elif not holes:
                new_proof = f"\n  ⟨{vlist}, {comp_refs},\n    {callterm}⟩\n"
            else:
                lines = [f"  refine ⟨{vlist}, {comp_refs},\n    {callterm}⟩"]
                for h, c in holes:
                    lines.append(f"  case {h} => exact {c}" if '\n' not in c else f"  case {h} =>\n    exact {c}")
                new_proof = ' by\n' + '\n'.join(lines) + '\n'
            old = src[st:en]
            if prelude:
                tail_raw = old[a + 2 + len(proof_cs.rstrip()):]
            else:
                tail_raw = old[a + 2 + off + endi + 1:]
            newtxt = old[:m.end()] + new_stm + ' :=' + new_proof
            newtxt = newtxt.rstrip('\n') + tail_raw.lstrip(' \t') if tail_raw.strip() == '' else newtxt + tail_raw
            edits.append((st, en, newtxt, full))
        except Manual as e:
            log('MANUAL', path, full, str(e))
    out = src
    for st, en, newtxt, full in sorted(edits, reverse=True):
        out = out[:st] + newtxt + out[en:]
        log('UPGRADED', path, full)
    return out

def main():
    args = sys.argv[1:]; dry = '--dry' in args
    files = [a for a in args if not a.startswith('--')]
    def log(*a): print(*a, flush=True)
    for f in files:
        src = open(f).read()
        new = upgrade(src, f, log)
        if new != src and not dry: open(f, 'w').write(new)

if __name__ == '__main__': main()
