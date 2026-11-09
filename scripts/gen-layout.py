#!/usr/bin/env python3
"""scripts/gen-layout.py check|regen [--order "g1 g2 .."] [LEAN_DIR]

The six generators scripts/gen-*.sh (TB / FM re-targetings of the IntoBig and Hex proofs) were written for the pre-split layout
(lean/Fv256/{Arm64,Amd64}/X.lean, one module = spec definitions + proofs).  They are kept UNCHANGED and run on a LEGACY VIEW:

  1. legacy view   every generator input module (IntoBig*, Hex, per ISA) is re-assembled from its Spec/ part and its Proofs/ part
                   (imports mapped back to the old module names with scripts/layout-map.json);
  2. generate      the unchanged generators run on the view (TB first, then FM, in the order given);
  3. split back    every generated module is cut again into a Spec/ part (the declarations whose qualified name is in the spec closure
                   recorded in layout-map.json) and a Proofs/ part (the rest), imports mapped to the new module names.
`check` compares the result with the committed lean/Fv256/{Spec,Proofs}/{Arm64,Amd64}/{TB,FM}; `regen` replaces those directories in place.
Nothing but those generated directories is ever written."""
import json, os, re, shutil, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leansplit as LS

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ISAS = ('Arm64', 'Amd64')
KINDS = ('TB', 'FM')


def load_map():
    return json.load(open(os.path.join(ROOT, 'scripts/layout-map.json')))


def mod_path(lean, mod):
    return os.path.join(lean, mod.replace('.', '/') + '.lean')


def body_cmds(text):
    return [c for c in LS.split(text) if c.kind != 'import']


def imports_of(text):
    return re.findall(r'^import\s+(\S+)', text, re.M)


# ------------------------------------------------------------------------------------------------------------- legacy view
def input_modules(lean):
    """old module names of the generator inputs found in the new layout"""
    out = []
    for isa in ISAS:
        d = os.path.join(lean, 'Fv256/Proofs', isa)
        for f in sorted(os.listdir(d)):
            if f.endswith('.lean') and (f.startswith('IntoBig') or f == 'Hex.lean'):
                out.append('Fv256.%s.%s' % (isa, f[:-5]))
    return out


def build_view(lean, view, M):
    p2old = {v: k for k, v in M['old2proof'].items()}
    s2old = {v: k for k, v in M['old2spec'].items()}
    back = lambda m: p2old.get(m, s2old.get(m, m))
    for old in input_modules(lean):
        P = open(mod_path(lean, M['old2proof'][old])).read()
        sp = M['old2spec'].get(old)
        S = open(mod_path(lean, sp)).read() if sp and os.path.exists(mod_path(lean, sp)) else ''
        imps = []
        for t in (P, S):
            for i in imports_of(t):
                j = back(i)
                if j != old and j not in imps:
                    imps.append(j)
        text = ''.join('import %s\n' % i for i in imps) + '\n'
        # Spec part first (its commands are definitions only), then the proofs part
        text += ''.join(S[c.start:c.end] for c in body_cmds(S))
        text += '\n' + ''.join(P[c.start:c.end] for c in body_cmds(P))
        dst = mod_path(view, old)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w').write(text)


# ------------------------------------------------------------------------------------------------------------- split back
DECL = re.compile(r'^(?:(?:private|protected|noncomputable|partial|nonrec)\s+)*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|nonrec)\s+)*'
                  r'(def|abbrev|theorem|lemma|structure|inductive|class|opaque)\s+([^\s:({\[⟨]+)')


def cmd_body_start(text):
    """strip a leading doc comment and `open .. in` / `set_option .. in` glue"""
    t = text.lstrip()
    while True:
        m = re.match(r'(?:open|set_option|attribute)\b[^\n]*\bin[ \t]*\n\s*', t)
        if not m: break
        t = t[m.end():]
    if t.startswith('/--'):
        d = 1; q = 3
        while q < len(t) and d:
            if t.startswith('/-', q): d += 1; q += 2
            elif t.startswith('-/', q): d -= 1; q += 2
            else: q += 1
        t = t[q:].lstrip()
    return t


def qualified_names(text, cmds):
    """qualified declared name (or None) for every command, tracking namespace / section nesting"""
    ns = []; stack = []; out = []
    for c in cmds:
        t = cmd_body_start(text[c.start:c.end])
        m = re.match(r'namespace\s+(\S+)', t)
        if m:
            parts = m.group(1).split('.'); ns += parts; stack.append(len(parts)); out.append(None); continue
        if re.match(r'section\b', t):
            stack.append(0); out.append(None); continue
        if re.match(r'end\b', t):
            k = stack.pop() if stack else 0
            if k: ns = ns[:-k]
            out.append(None); continue
        m = DECL.match(t)
        if m:
            nm = m.group(2)
            out.append(nm[len('_root_.'):] if nm.startswith('_root_.') else '.'.join(ns + [nm]))
        else:
            out.append(None)
    return out


CTX = LS.CTX_KINDS


def prune_empty_namespaces(chunks):
    """chunks: list of (kind, text); drop `namespace N .. end N` pairs that contain only context commands (opens, set_options)"""
    res = []; i = 0
    while i < len(chunks):
        k, t = chunks[i]
        if k == 'namespace':
            depth = 0; j = i; ok = True
            while j < len(chunks):
                kk = chunks[j][0]
                if kk in ('namespace', 'section'): depth += 1
                elif kk == 'end':
                    depth -= 1
                    if depth == 0: break
                elif kk not in ('open', 'set_option', 'variable', 'universe', 'export'): ok = False
                j += 1
            if ok and j < len(chunks) and depth == 0:
                i = j + 1; continue
        res.append((k, t)); i += 1
    return res


def split_generated(text, names, M, gen_spec):
    """returns (spec_text or None, proof_text); gen_spec: dict old generated module -> spec module name (filled progressively)"""
    cmds = LS.split(text)
    qn = qualified_names(text, cmds)
    spec_idx = {i for i, c in enumerate(cmds) if qn[i] in names}
    head_end = min((c.start for c in cmds if c.kind != 'import'), default=len(text))
    imps = imports_of(text[:head_end])
    return cmds, spec_idx, imps


def map_imports(imps, M, gen_proof, gen_spec):
    proof, spec = [], []
    for y in imps:
        if y in gen_proof:
            proof.append(gen_proof[y])
            spec += gen_spec.get(y, [])
        elif y.startswith('Fv256'):
            proof.append(M['old2proof'].get(y, y))
            spec += [M['old2spec'][x] for x in M['specdeps'].get(y, [])]
        else:
            proof.append(y); spec.append(y)
    return proof, spec


def gen_name(isa, kind, m):
    return 'Fv256.%s.%s.%s' % (isa, kind, m)


def split_back(view, out, M):
    names = set(M['names'])
    gens = {}   # old generated module -> (isa, kind, base)
    for isa in ISAS:
        for kind in KINDS:
            d = os.path.join(view, 'Fv256', isa, kind)
            if os.path.isdir(d):
                for f in sorted(os.listdir(d)):
                    if f.endswith('.lean'): gens[gen_name(isa, kind, f[:-5])] = (isa, kind, f[:-5])
    gen_proof = {g: 'Fv256.Proofs.%s.%s.%s' % (v[0], v[1], v[2]) for g, v in gens.items()}
    gen_spec = {}
    done = set(); order = []
    texts = {g: open(mod_path(view, g)).read() for g in gens}
    while len(order) < len(gens):          # dependency order among generated modules
        prog = False
        for g in sorted(gens):
            if g in done: continue
            if all((i not in gens) or (i in done) for i in imports_of(texts[g])):
                order.append(g); done.add(g); prog = True
        if not prog: sys.exit('gen-layout: import cycle among generated modules')
    for g in order:
        isa, kind, base = gens[g]
        text = texts[g]
        cmds = LS.split(text)
        qn = qualified_names(text, cmds)
        spec_idx = {i for i, c in enumerate(cmds) if qn[i] in names and c.kind in LS.DECL_KINDS}
        head_end = min((c.start for c in cmds if c.kind != 'import'), default=len(text))
        pimps, simps = map_imports(imports_of(text[:head_end]), M, gen_proof, gen_spec)
        sname = 'Fv256.Spec.%s.%s.%s' % (isa, kind, base)
        pname = gen_proof[g]
        if spec_idx:
            simps_u = sorted({x for x in simps if x != sname})
            chunks = []
            for i, c in enumerate(cmds):
                body = text[c.start:c.end]
                if c.kind in ('import', 'comment'): continue
                if i in spec_idx:
                    body = re.sub(r'^(\s*(?:/--(?:.|\n)*?-/\s*)?(?:@\[[^\]]*\]\s*)*)private\s+', r'\1', body, count=1)
                    chunks.append(('decl', body.rstrip('\n') + '\n'))
                elif c.kind in CTX:
                    chunks.append((c.kind, body.rstrip('\n') + '\n'))
            chunks = prune_empty_namespaces(chunks)
            stext = ''.join('import %s\n' % x for x in simps_u) + '\n/-! SPECIFICATION part (generated): the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/\n\n' + '\n'.join(t for _, t in chunks)
            dst = mod_path(out, sname); os.makedirs(os.path.dirname(dst), exist_ok=True); open(dst, 'w').write(stext)
            gen_spec[g] = [sname]
            pimps = pimps + [sname]
        else:
            gen_spec[g] = sorted({x for x in simps})
        keep = [(c.kind, text[c.start:c.end]) for i, c in enumerate(cmds) if i not in spec_idx and c.kind != 'import']
        ptext = ''.join('import %s\n' % x for x in dict.fromkeys(pimps)) + '\n' + ''.join(t for _, t in keep)
        dst = mod_path(out, pname); os.makedirs(os.path.dirname(dst), exist_ok=True); open(dst, 'w').write(ptext)
    return gens


def run(lean, out, order):
    M = load_map()
    view = tempfile.mkdtemp(prefix='genview.', dir=os.environ.get('TMPDIR'))
    try:
        build_view(lean, view, M)
        # TB generators read their own inputs; FM generators read the generated TB modules: all inside the view
        for g in order:
            r = subprocess.run(['bash', os.path.join(ROOT, 'scripts', g + '.sh'), view], capture_output=True, text=True)
            if r.returncode != 0:
                sys.exit('gen-layout: FAIL: scripts/%s.sh failed on the legacy view:\n%s' % (g, (r.stdout + r.stderr)[-600:]))
        return split_back(view, out, M)
    finally:
        shutil.rmtree(view, ignore_errors=True)


def gen_dirs(lean):
    return [os.path.join(lean, 'Fv256', k, isa, kd) for k in ('Spec', 'Proofs') for isa in ISAS for kd in KINDS]


def main():
    a = sys.argv[1:]
    if not a or a[0] not in ('check', 'regen'): sys.exit(__doc__)
    cmd = a[0]; a = a[1:]
    order = 'gen-tb-intobig gen-tb-intobig-amd64 gen-fm-hex-arm64 gen-fm-hex-amd64 gen-fm-intobig-arm64 gen-fm-intobig-amd64'.split()
    if a[:1] == ['--order']: order = a[1].split(); a = a[2:]
    lean = a[0] if a else os.path.join(ROOT, 'lean')
    out = tempfile.mkdtemp(prefix='genout.', dir=os.environ.get('TMPDIR'))
    try:
        run(lean, out, order)
        if cmd == 'regen':
            for d in gen_dirs(lean): shutil.rmtree(d, ignore_errors=True)
            for k in ('Spec', 'Proofs'):
                for isa in ISAS:
                    for kd in KINDS:
                        s = os.path.join(out, 'Fv256', k, isa, kd)
                        if os.path.isdir(s):
                            shutil.copytree(s, os.path.join(lean, 'Fv256', k, isa, kd))
            print('gen-layout: regenerated TB/FM modules'); return 0
        bad = 0
        for d in gen_dirs(lean):
            rel = os.path.relpath(d, lean)
            o = os.path.join(out, rel)
            r = subprocess.run(['diff', '-ru', d, o] if os.path.isdir(d) and os.path.isdir(o) else ['true'], capture_output=True, text=True)
            if os.path.isdir(d) != os.path.isdir(o):
                print('gen-layout: FAIL: %s %s in the committed tree / generator output' % (rel, 'exists' if os.path.isdir(d) else 'missing')); bad = 1
            elif r.returncode != 0:
                print('gen-layout: FAIL: %s differs from the generators\' output:' % rel); print(r.stdout[:3000]); bad = 1
        print('gen-layout check: %s' % ('FAILED' if bad else 'OK'))
        return bad
    finally:
        shutil.rmtree(out, ignore_errors=True)


if __name__ == '__main__':
    sys.exit(main())
