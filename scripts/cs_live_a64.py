#!/usr/bin/env python3
"""cs_live_a64.py -- arm64 call-site (U-WITNESS-CALLSITE) conjuncts for the toy-runtime "Live" witnesses
(SetFromDecimal / FromDecimal / MustFromDecimal / UnmarshalJSON / UnmarshalText / Scan ...).

  cs_live_a64.py NAME CORE_FILE CORE_THM THIN_FILE THIN_THM [THIN_THM ...]
  cs_live_a64.py NAME --print                (print block + conjuncts only)

NAME selects a CFG entry below. The block (defs + pre lemmas) is inserted before the doc comment of CORE_THM in CORE_FILE; the
conjunct list is appended to CORE_THM's statement (before the first `:=` that is followed by the anonymous-constructor proof)
and the proof terms before the last `⟩` of its proof; THIN_FILE's THIN_THM(s) get the conjuncts before `Returns (`,
the extra binders `cs1..` in `obtain ... := <core>` and the extra components in the `exact ⟨..., correctness ...⟩`.
Idempotent per file (marker CALLSITE-LIVE-BLOCK). ALWAYS `git checkout fv/wrun -- FILE` first when re-running.

Conjunct shapes (closed L := [], b := 0x400, via inv0):
  newobject : ∃ s_c, s_c.pc = ofNat A ∧ NewobjectLiveSite R A 4096 [] 0x400 s_c
  mallocgc  : MallocgcLiveSite ; memmove : MemmoveLiveSite R A 4096 ; wb n : WbLiveSite R A 4096 n
  cmpstring : CmpstringPre 16 s_c ; ifaceeq : IfaceeqSite R2 s_c        (Site wrappers: lean/Fv256/Arm64/CallSites/Base.lean)
CFG keys: s0 (state name), R2 (term), priv (simp lemma name of R2.priv), pos (position of each stub in `ok`: new w1 w2 mg mv),
  nok (number of disjuncts of `ok`), new_ok / mg_ok / mv_ok (proof of the inner conj after `Or` position), regs (dict: mv/mg/new args),
  rt_eq, inv0, env0 (env0 : Env .. s0), extra (list of (defs, conj, term): hook for RtLive etc.).
"""
import sys, re

def okpos(i, n, x):
    if i == n - 1:
        return 'Or.inr (' * i + x + ')' * i
    return 'Or.inr (' * i + 'Or.inl (' + x + ')' + ')' * i

A = lambda x: f'(Extracted.program.contractAddr "{x}")'
NAMES = dict(new='runtime.newobject', w1='runtime.gcWriteBarrier1', w2='runtime.gcWriteBarrier2', mg='runtime.mallocgc',
             mv='runtime.memmove', cm='runtime.cmpstring', If='runtime.ifaceeq')

CFG = {
 'sfd': dict(s0='s0', R2='R0', priv='R0_priv', nok=5, pos=dict(new=0, w1=1, w2=2, mg=3, mv=4), newty='numErrT',
             new_ok='⟨rfl, by decide⟩', mg_ok='⟨rfl, by decide⟩', mv_ok='⟨rfl, zW, by decide⟩', dst='zW', src='0x301000',
             core_extra_import=None),
 'fd': dict(s0='s0', R2='(R3 TW)', priv='R3_priv', nok=6, pos=dict(new=0, w1=2, w2=3, mg=4, mv=5), newty='numErrT',
            new_ok='⟨rfl, by decide⟩', mg_ok='⟨rfl, 1, by decide, by decide, by decide⟩',
            mv_ok='⟨rfl, zW, 0x301000, 1, by decide, by decide, by decide⟩', dst='zW', src='0x301000'),
}
CFG['mfd'] = dict(CFG['fd'])

def block(c):
    S = c['s0']; N = c['nok']; P = c['pos']; RT = c.get('rt_eq', 'rt_eq'); inv = c.get('inv0', 'inv0'); env = c.get('env0', 'env0')
    R2 = c['R2']; priv = c['priv']
    d = []
    d.append(f'''/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `{S}` with `PC` at the stub's entry and the argument registers of a request `ok` serves. -/
def csNew0 : State := {{ {S} with regs := fun i => if i = 0 then BitVec.ofNat 64 {c['newty']} else {S}.regs i }}
def csNew : State := {{ csNew0 with pc := BitVec.ofNat 64 {A(NAMES['new'])} }}
def csMg0 : State := {{ {S} with regs := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 0 else {S}.regs i }}
def csMg : State := {{ csMg0 with pc := BitVec.ofNat 64 {A(NAMES['mg'])} }}
def csMv0 : State := {{ {S} with regs := fun i => if i = 0 then BitVec.ofNat 64 {c['dst']} else if i = 1 then BitVec.ofNat 64 {c['src']} else if i = 2 then 1 else {S}.regs i }}
def csMv : State := {{ csMv0 with pc := BitVec.ofNat 64 {A(NAMES['mv'])} }}
def csW1 : State := {{ {S} with pc := BitVec.ofNat 64 {A(NAMES['w1'])} }}
def csW2 : State := {{ {S} with pc := BitVec.ofNat 64 {A(NAMES['w2'])} }}
def csCm0 : State := {{ {S} with regs := fun i => if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 0 else {S}.regs i }}
def csCm : State := {{ csCm0 with pc := BitVec.ofNat 64 {A(NAMES['cm'])} }}
def csIf0 : State := {{ {S} with regs := fun i => if i = 0 then 0 else {S}.regs i }}
def csIf : State := {{ csIf0 with pc := BitVec.ofNat 64 {A(NAMES['If'])} }}
''')
    sep = f'''  · intro r hr
    rw [{RT}]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)'''
    sep1 = f'''  intro r hr
  rw [{RT}]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide'''
    cok = 'callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)'
    gok = 'guardOK_of (by decide) (by decide) (by decide)'
    ok = lambda k, x: okpos(P[k], N, x)
    d.append(f'''set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R {A(NAMES['new'])} 4096 [] 0x400 csNew := by
  refine ⟨⟨{cok}, typeOK_of (by decide) (by decide), by decide⟩, ⟨{gok}, by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, {inv}, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact {ok('new', c['new_ok'])}
{sep}

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R {A(NAMES['mg'])} 4096 [] 0x400 csMg := by
  refine ⟨⟨{cok}, by decide, Or.inl (by decide)⟩, ⟨{gok}, by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, {inv}, by decide, liveSep_nil _, ?_⟩
  · rw [addr_mg]; exact {ok('mg', c['mg_ok'])}
{sep}

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R {A(NAMES['mv'])} 4096 [] 0x400 csMv := by
  refine ⟨⟨(guardOK_iff _ _).1 ({gok}), {cok}, by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ⟨?_, {inv}, liveSep_nil _, ?_⟩, ⟨by decide, by decide, by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    by decide, by decide, by simp only [calleeStack, outside_cons, outside_nil]; decide, Or.inr (by rw [{RT}]; simp only [outside_cons, outside_nil]; decide)⟩
  · rw [addr_mv]; exact {ok('mv', c['mv_ok'])}
{sep}

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R {A(NAMES['w1'])} 4096 1 [] 0x400 csW1 := by
  refine ⟨{cok}, by rw [addr_w1]; exact {ok('w1', '⟨rfl, rfl⟩')}, {inv}, liveSep_nil _, ?_⟩
{sep1}

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R {A(NAMES['w2'])} 4096 2 [] 0x400 csW2 := by
  refine ⟨{cok}, by rw [addr_w2]; exact {ok('w2', '⟨rfl, rfl⟩')}, {inv}, liveSep_nil _, ?_⟩
{sep1}

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 csCm :=
  ⟨{cok}, Or.inl (by decide), Or.inl (by decide)⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite {R2} csIf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := {env}
  refine ⟨⟨hE, (guardOK_iff _ _).1 ({gok}), {cok}, ?_⟩, fun h => absurd (by decide) h⟩
  simp only [{priv}]; apply outside_of_decide; decide
''')
    for e in c.get('extra', []): d.append(e[0])
    ents = {k: A(v) for k, v in NAMES.items()}
    site = lambda s, body: f'(∃ (s_c : State), s_c.pc = BitVec.ofNat 64 {ents[s]} ∧ {body})'
    conj = [
      site('new', f'NewobjectLiveSite R {ents["new"]} 4096 [] 0x400 s_c'),
      site('mg', f'MallocgcLiveSite R {ents["mg"]} 4096 [] 0x400 s_c'),
      site('mv', f'MemmoveLiveSite R {ents["mv"]} 4096 [] 0x400 s_c'),
      site('w1', f'WbLiveSite R {ents["w1"]} 4096 1 [] 0x400 s_c'),
      site('w2', f'WbLiveSite R {ents["w2"]} 4096 2 [] 0x400 s_c'),
      site('cm', 'Janus.Contracts.Cmpstring.CmpstringPre 16 s_c'),
      site('If', 'IfaceeqSite R2 s_c'),
    ]
    terms = ['⟨csNew, rfl, csNew_pre⟩', '⟨csMg, rfl, csMg_pre⟩', '⟨csMv, rfl, csMv_pre⟩', '⟨csW1, rfl, csW1_pre⟩',
             '⟨csW2, rfl, csW2_pre⟩', '⟨csCm, rfl, csCm_pre⟩', '⟨csIf, rfl, csIf_pre⟩']
    for e in c.get('extra', []): conj.append(e[1]); terms.append(e[2])
    return ''.join(d), conj, terms

def add_header(s, nsname):
    if 'import Fv256.Arm64.CallSites.Base' not in s:
        s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    if 'open Fv256.Arm64.CallSites' not in s:
        i = s.index('namespace ' + nsname)
        s = s[:i] + 'open Fv256.Arm64.CallSites\n\n' + s[i:]
    return s

def thm_span(s, name, nth=0):
    ms = list(re.finditer(r'^theorem\s+' + re.escape(name) + r'\b', s, re.M))
    m = ms[nth]
    nxt = re.search(r'^(theorem|lemma|def|abbrev|end|namespace|/--|set_option|open|@\[)\b', s[m.end():], re.M)
    return m.start(), m.end() + (nxt.start() if nxt else len(s) - m.end())

def apply(name, cfile, cthm, tfile, tthms, nsc):
    c = CFG[name]
    defs, conj, terms = block(c)
    s = open(cfile).read()
    assert 'CALLSITE-LIVE-BLOCK' not in s, 'already applied'
    s = add_header(s, nsc)
    st, en = thm_span(s, cthm)
    # block before the docstring/set_option preceding the theorem
    j = st
    pre = s[:st].rstrip('\n')
    if pre.endswith('-/'): j = pre.rindex('/--')
    lines = s[:j].rstrip('\n').split('\n')
    if lines and lines[-1].startswith('set_option') and lines[-1].rstrip().endswith(' in'):
        j = len('\n'.join(lines[:-1])) + 1
    s = s[:j] + '-- CALLSITE-LIVE-BLOCK\n' + defs + '\n' + s[j:]
    st, en = thm_span(s, cthm)
    body = s[st:en]
    k = re.search(r' :=\n\s*⟨', body).start()
    body = body[:k] + ' ∧\n    ' + ' ∧\n    '.join(conj) + body[k:]
    e = body.rindex('⟩')
    body = body[:e].rstrip() + ',\n    ' + ', '.join(terms) + body[e:]
    s = s[:st] + body + s[en:]
    open(cfile, 'w').write(s)
    t = open(tfile).read()
    t = add_header(t, re.search(r'^namespace (\S+)', t, re.M).group(1))
    for thm in tthms:
        st, en = thm_span(t, thm)
        body = t[st:en]
        r = re.search(r'^    (Go)?Returns \(', body, re.M).start()
        body = body[:r] + '    ' + ' ∧\n    '.join(conj) + ' ∧\n' + body[r:]
        names = ', '.join(f'cs{i+1}' for i in range(len(terms)))
        m = re.search(r', (\w+)⟩ := ', body)
        body = body[:m.start()] + f', {m.group(1)}, {names}⟩ := ' + body[m.end():]
        q = re.search(r'(\w+),\n\s*correctness ', body)
        body = body[:q.start()] + f'{q.group(1)}, {names},\n    correctness ' + body[q.end():]
        t = t[:st] + body + t[en:]
    open(tfile, 'w').write(t)

# ---------------------------------------------------------------------------------------------------------------
# inline_thin: the auditor's witness-size walk (Audit.lean `witnessSizes`/`proofHead`, U-ICALL-STACK) cannot read through
# `obtain ⟨..⟩ := core; exact ⟨..⟩` (stuck at `Exists.rec` on the theorem constant `core`). Rewrite the thin witness's proof
# as one `refine ⟨<core components>, correctness ..⟩` (proof components as `?name` holes closed by `case name => exact (..)`).
#   cs_live_a64.py --inline CORE_FILE CORE_THM THIN_FILE THIN_THM [OPEN_NS]
def split_top(s):
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '⟨([{': depth += 1
        elif ch in '⟩)]}': depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur.strip()); cur = ''
        else: cur += ch
    if cur.strip(): out.append(cur.strip())
    return out

def inline_thin(cfile, cthm, tfile, tthm, open_ns=None):
    s = open(cfile).read()
    st, en = thm_span(s, cthm); body = s[st:en]
    k = re.search(r' :=\n\s*⟨', body).end()
    e = body.rindex('⟩')
    comps = split_top(body[k:e])
    t = open(tfile).read()
    st, en = thm_span(t, tthm); tb = t[st:en]
    m = re.search(r'\n(\s*)obtain ⟨(.*?)⟩ := \S+\n\s*exact ⟨(.*)⟩\s*$', tb, re.S)
    assert m, 'thin proof shape not recognised'
    ind = m.group(1)
    names = [x.strip() for x in m.group(2).split(',')]
    assert len(names) == len(comps), (len(names), len(comps))
    cor = m.group(3)[m.group(3).index('correctness'):]
    ndata = names.index('s') + 1
    simple = re.compile(r"^[\w.'«»]+$")
    sub, cases = {}, []
    for i, (n, c) in enumerate(zip(names, comps)):
        c1 = ' '.join(c.split())
        if simple.match(c1): sub[n] = c1
        elif i < ndata: sub[n] = '(' + c1 + ')'
        else:
            sub[n] = '?' + n; cases.append(f'{ind}case {n} => exact ({c1})')
    tup = ', '.join(sub[n] for n in names)
    cor2 = ' '.join(sub.get(x, x) for x in cor.split())
    proof = f'\n{ind}refine ⟨{tup},\n{ind}  {cor2}⟩\n' + '\n'.join(cases) + '\n'
    tb = tb[:m.start()] + proof + '\n'
    t = t[:st] + tb + t[en:]
    if open_ns and f'open {open_ns}\n' not in t:
        t = t.replace('\nnamespace Witness\n', f'\nnamespace Witness\nopen {open_ns}\n', 1)
    open(tfile, 'w').write(t)


if __name__ == '__main__':
    n = sys.argv[1]
    if n == '--inline':
        a = sys.argv[2:]; inline_thin(a[0], a[1], a[2], a[3], a[4] if len(a) > 4 else None); sys.exit(0)
    if sys.argv[2] == '--print':
        d, cj, tm = block(CFG[n]); print(d); print('\n'.join(cj)); print(tm); sys.exit(0)
    cf, ct, tf = sys.argv[2:5]; tt = sys.argv[5:]
    nsc = re.search(r'^namespace (\S+)', open(cf).read(), re.M).group(1)
    apply(n, cf, ct, tf, tt, nsc)

