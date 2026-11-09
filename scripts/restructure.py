#!/usr/bin/env python3
"""scripts/restructure.py -- split lean/Fv256 into  Spec/  (everything a final theorem STATEMENT depends on)  and  Proofs/{Arm64,Amd64,Common}.

Idempotent: if lean/Fv256/Proofs already exists the script reports `already restructured` and exits 0 without touching anything.
NAMESPACES are never changed (theorem names such as Fv256.Amd64.Format.correctness stay); only module paths move.

  1. SURVEY   scripts/spec_survey.py elaborates every final theorem (correctness + existential witnesses) with proofs replaced by
              `sorry` and collects the Fv256 constants reachable from its TYPE through definitions (Janus.* / Extracted.* excluded).
              (or --closure FILE to reuse an earlier survey of the SAME tree).
  2. PLAN     per old module M: whole-move to Spec/ if all its declarations are in the closure, split if only some are, else Proofs only.
  3. APPLY    git mv + write; rewrite every `import`, scripts (verify-all, contract-flags, ...), lakefile, docs path mentions.

Layout produced (module -> file under lean/):
  Fv256.Spec         -> Fv256.Spec.Core ;  Fv256.SpecB -> Fv256.Spec.B ; other Fv256.Spec<X> -> Fv256.Spec.<X>
  Fv256.Arm64.X      -> Fv256.Proofs.Arm64.X   (spec part: Fv256.Spec.Arm64.X)
  Fv256.Amd64.X      -> Fv256.Proofs.Amd64.X   (spec part: Fv256.Spec.Amd64.X)      Fv256.Amd64v3.X -> Fv256.Proofs.Amd64v3.X
  Fv256.X (shared)   -> Fv256.Proofs.Common.X  (spec part: Fv256.Spec.X)
usage: scripts/restructure.py [--closure FILE] [--survey-out FILE] [--plan-only] [--dry]
"""
import argparse, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leansplit as LS

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GEN_RX = re.compile(r'/(Arm64|Amd64)/(TB|FM)/')
os.chdir(ROOT)
L = 'lean'
FV = 'lean/Fv256'


def sh(cmd, **kw):
    r = subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True, **kw)
    return r


def git(*a):
    r = subprocess.run(['git'] + list(a), capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit('git %s failed: %s' % (' '.join(a), r.stderr))
    return r.stdout


# ---------------------------------------------------------------------------------------------------------------- naming
def mod_of(path):            # lean/Fv256/Arm64/Add.lean -> Fv256.Arm64.Add
    return path[len(L) + 1:-5].replace('/', '.')


def path_of(mod):
    return L + '/' + mod.replace('.', '/') + '.lean'


def proof_name(m):
    p = m.split('.')
    assert p[0] == 'Fv256'
    if len(p) >= 2 and p[1] in ('Arm64', 'Amd64', 'Amd64v3'):
        return '.'.join(['Fv256', 'Proofs'] + p[1:])
    return '.'.join(['Fv256', 'Proofs', 'Common'] + p[1:])


def spec_name(m):
    p = m.split('.')
    if len(p) >= 2 and p[1] in ('Arm64', 'Amd64', 'Amd64v3'):
        return '.'.join(['Fv256', 'Spec'] + p[1:])
    if len(p) == 2 and p[1].startswith('Spec'):
        rest = p[1][4:]
        return 'Fv256.Spec.' + (rest if rest else 'Core')
    return '.'.join(['Fv256', 'Spec'] + p[1:])


# ---------------------------------------------------------------------------------------------------------------- survey
def load_closure(a):
    if a.closure:
        return json.load(open(a.closure))
    out = a.survey_out or 'build/spec-closure.json'
    env = dict(os.environ)
    r = subprocess.run([sys.executable, 'scripts/spec_survey.py', '--out', out], env=env)
    if r.returncode != 0:
        sys.exit('survey failed')
    return json.load(open(out))


def resolve(consts):
    """consts: list of dicts (name, module, kind, range); returns {module: set(line numbers)} (start lines of closure declarations)"""
    byname = {(c['name'], c['module']): c for c in consts}
    res = {}
    bad = []
    for c in consts:
        cur = c
        name = c['name']
        while cur['range'] == '-':
            if '.' not in name:
                cur = None; break
            name = name.rsplit('.', 1)[0]
            cur = byname.get((name, c['module']))
            if cur is None:
                break
        if cur is None:
            bad.append(c['name']); continue
        a, b = cur['range'].split('-')
        l0 = int(a.split(':')[0]); l1 = int(b.split(':')[0])
        res.setdefault(cur['module'], set()).add((l0, l1))
    return res, bad


# ---------------------------------------------------------------------------------------------------------------- plan
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--closure'); ap.add_argument('--survey-out'); ap.add_argument('--plan-only', action='store_true')
    a = ap.parse_args()
    if os.path.isdir(FV + '/Proofs'):
        print('restructure: lean/Fv256/Proofs exists: already restructured, nothing to do'); return
    if sh(['git', 'status', '--porcelain', '--untracked-files=no']).stdout.strip():
        sys.exit('restructure: working tree not clean (commit first)')
    sv = load_closure(a)
    allc = {}
    errors = [(k, v['error']) for k, v in sv.items() if 'error' in v]
    if errors:
        for k, e in errors: print('survey error', k, e[:200])
        sys.exit('survey incomplete')
    for k, v in sv.items():
        for c in v['consts']:
            allc[(c['name'], c['module'])] = c      # the same name can live in several modules (TB/FM copies of IntoBigDefs)
    roots = {r for v in sv.values() for r in v['roots']}
    # auxiliary constants of a final theorem's own statement (Witness.nonvacuous.match_1, ...) belong to the theorem, which stays in Proofs/
    allc = {k: c for k, c in allc.items() if not any(c['name'].startswith(r + '.') for r in roots)}
    consts = list(allc.values())
    lines_by_mod, bad = resolve(consts)
    if bad:
        sys.exit('unresolvable aux constants (no declaration range): %s' % bad[:10])
    # real modules of closure constants: the survey reports the final-theorem module for `<cur>` constants
    files = {}
    generated = []   # TB/FM modules are produced by scripts/gen-*.sh: they are regenerated (scripts/gen-layout.py), never moved or split
    for r, _, fs in os.walk(FV):
        for f in fs:
            if f.endswith('.lean'):
                p_ = os.path.join(r, f)
                if GEN_RX.search(p_): generated.append(p_); continue
                files[mod_of(p_)] = p_
    plan = {}        # old module -> dict(kind=whole|split|proof, moved=[cmd idx], cmds, text)
    for m, p in sorted(files.items()):
        text = open(p).read()
        cmds = LS.split(text)
        moved = set()
        for (l0, l1) in lines_by_mod.get(m, ()):
            hit = [i for i, c in enumerate(cmds) if c.line0 <= l0 <= c.line1 and c.kind in LS.DECL_KINDS | {'macro', 'elab', 'syntax', 'notation'}]
            if not hit:
                sys.exit('%s: closure declaration at line %d is not inside a recognised command' % (p, l0))
            if cmds[hit[0]].line0 != l0 and not (cmds[hit[0]].line0 < l0):
                sys.exit('%s:%d decl start mismatch' % (p, l0))
            moved.add(hit[0])
        kind = 'split' if moved else 'proof'     # a module whose declarations are ALL in the closure still keeps a (near empty) Proofs file:
        #                                           importers' transitive proof imports must not be lost
        plan[m] = dict(kind=kind, moved=sorted(moved), cmds=cmds, text=text, path=p)
    nm = {k: sum(1 for v in plan.values() if v['kind'] == k) for k in ('split', 'proof')}
    print('plan: %(split)d modules with a Spec part, %(proof)d proof-only modules; closure constants %(n)d' % dict(nm, n=len(consts)))
    mapping = {}      # old module -> new module for imports
    for m, v in plan.items():
        mapping[m] = proof_name(m)
    spec_of = {m: spec_name(m) for m, v in plan.items() if v['kind'] == 'split'}
    for (n_, mod_) in allc:
        if mod_ not in plan and GEN_RX.search('/' + mod_.replace('.', '/') + '.lean'):
            spec_of[mod_] = spec_name(mod_); mapping[mod_] = proof_name(mod_)
    old_imports = {m: re.findall(r'^import\s+(Fv256[\w.]*)', v['text'], re.M) for m, v in plan.items()}
    for g_ in generated:      # generated modules take part in the spec-dependency graph through their (pre-regeneration) imports
        old_imports[mod_of(g_)] = re.findall(r'^import\s+(Fv256[\w.]*)', open(g_).read(), re.M)
    own_consts = {}
    for (n, mod) in allc:
        own_consts.setdefault(mod, set()).add(n)
    sdeps_memo = {}
    def spec_deps(x):
        """nearest Spec modules among the (transitive through proof-only modules) imports of old module x"""
        if x in spec_of: return {x}
        if x not in sdeps_memo:
            r = set()
            for y in old_imports.get(x, []): r |= spec_deps(y)
            sdeps_memo[x] = r
        return sdeps_memo[x]
    prov_memo = {}
    def provided(x):
        """constants provided by the Spec part of old module x (own + everything its Spec imports provide)"""
        if x not in prov_memo:
            prov_memo[x] = set()
            r = set(own_consts.get(x, ()))
            for y in old_imports.get(x, []):
                for z in spec_deps(y): r |= provided(z)
            prov_memo[x] = r
        return prov_memo[x]
    os.makedirs('build', exist_ok=True)
    json.dump({'split': sorted(m for m, v in plan.items() if v['kind'] == 'split'),
               'consts': sorted('%s %s' % k for k in allc)}, open('build/restructure-plan.json', 'w'), indent=1)
    if a.plan_only:
        return
    # ------------------------------------------------------------------------------------------------ apply
    def fix_imports(text, own_is_spec):
        out = []
        for ln in text.split('\n'):
            m = re.match(r'^(\s*import\s+)(Fv256[\w.]*)(\s*(?:--.*)?)$', ln)
            if m:
                old = m.group(2)
                if own_is_spec:
                    if old in spec_of:
                        out.append(m.group(1) + spec_of[old])
                    # imports of pure-proof modules are dropped from spec files
                else:
                    if old not in mapping and re.match(r'Fv256\.(Arm64|Amd64|Amd64v3)\.', old):
                        out.append(m.group(1) + proof_name(old) + m.group(3))     # generated TB/FM modules
                    else:
                        out.append(m.group(1) + mapping.get(old, old) + m.group(3))
            else:
                out.append(ln)
        return '\n'.join(out)

    def split_imports(text):
        """separate the leading import block from the rest"""
        lines = text.split('\n')
        i = 0
        head = []
        while i < len(lines) and (lines[i].startswith('import ') or lines[i].strip() == ''):
            head.append(lines[i]); i += 1
        return head, '\n'.join(lines[i:])

    newfiles = {}   # path -> text
    moves = []      # (old path, new path)
    for m, v in plan.items():
        p, text, cmds = v['path'], v['text'], v['cmds']
        newp = path_of(proof_name(m))
        moves.append((p, newp))
        if v['kind'] == 'proof':
            newfiles[newp] = fix_imports(text, False)
            continue
        # split: the spec file gets context commands + moved declarations, the proof file the rest and an import of the spec file
        head_end = min((c.start for c in cmds if c.kind != 'import'), default=len(text))
        imports = [c for c in cmds if c.kind == 'import']
        head = text[:head_end]
        sd = set()
        for y in old_imports[m]: sd |= spec_deps(y)
        himp = [ln for ln in head.split('\n') if re.match(r'^\s*import\s+', ln) and not re.match(r'^\s*import\s+Fv256', ln)]
        spec_parts = ['\n'.join(himp + ['import ' + spec_name(y) for y in sorted(sd)]), '']
        prov = provided(m)
        kc = prov
        kn = {'Fv256'}
        for n in prov:
            parts = n.split('.')
            for i in range(1, len(parts)): kn.add('.'.join(parts[:i]))
        spec_parts.insert(1, '\n/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/\n')
        chunks = []
        for i, c in enumerate(cmds):
            if c.kind == 'import' or c.kind == 'comment':
                continue
            body = text[c.start:c.end]
            if i in v['moved']:
                body = re.sub(r'^(\s*(?:/--(?:.|\n)*?-/\s*)?(?:@\[[^\]]*\]\s*)*)private\s+', r'\1', body, count=1)
                chunks.append(('decl', body.rstrip('\n') + '\n'))
            elif c.kind in LS.CTX_KINDS:
                body = filter_ctx(body, kn, kc)
                if body:
                    chunks.append((c.kind, body.rstrip('\n') + '\n'))
        spec_parts += [t for _, t in LS.prune_empty_namespaces(chunks)]
        newfiles[path_of(spec_name(m))] = '\n'.join(spec_parts)
        keep = []
        for i, c in enumerate(cmds):
            if i in v['moved'] or c.kind == 'import':
                continue
            keep.append(text[c.start:c.end])
        # proof file: original head (imports rewritten) + import of the spec part + remaining commands
        proof = fix_imports(head, False)
        hl = proof.rstrip('\n').split('\n')
        # place the spec import after the last import line
        idx = max((k for k, ln in enumerate(hl) if ln.startswith('import ')), default=-1)
        hl.insert(idx + 1, 'import ' + spec_name(m))
        proof = '\n'.join(hl) + '\n\n' + ''.join(keep)
        # the `comment` command kind (module doc) is part of `keep` already; imports are in head
        newfiles[newp] = proof
    # tracked non-.lean files under lean/Fv256 (generator side files) follow their directory
    for f in git('ls-files', FV).split('\n'):
        if f and not f.endswith('.lean'):
            rel = f[len(FV) + 1:].split('/')
            tgt = FV + '/Proofs/' + ('/'.join(rel) if rel[0] in ('Arm64', 'Amd64', 'Amd64v3') else 'Common/' + '/'.join(rel))
            moves.append((f, tgt))
    # apply moves
    for old, new in moves:
        os.makedirs(os.path.dirname(new), exist_ok=True)
        git('mv', old, new)
    for p, t in newfiles.items():
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, 'w').write(t)
    for r, ds, fs in os.walk(FV, topdown=False):      # directories emptied by the moves
        if r not in (FV, FV + '/Spec', FV + '/Proofs') and not os.listdir(r):
            os.rmdir(r)
    # root file: the Extracted-free spec modules (umbrella Fv256.Spec) + the extraction-independent proof modules
    root = open(L + '/Fv256.lean').read()
    open(L + '/Fv256.lean', 'w').write(fix_imports(root, False).replace('import Fv256.Proofs.Common.Spec\n', 'import Fv256.Spec\n'))
    write_umbrella()
    rewrite_scripts(mapping)
    wire_checks()
    # generated TB/FM modules: removed here and regenerated by the (unchanged) generators on a legacy view, see scripts/gen-layout.py
    for g in generated:
        if os.path.exists(g): git('rm', '-q', '-f', g)
    layout_map = {'old2proof': {m: proof_name(m) for m in plan}, 'old2spec': spec_of,
                  'specdeps': {m: sorted(spec_deps(m)) for m in plan},
                  'names': sorted({n for (n, _) in allc}),
                  # per OLD module: the qualified names of its spec-closure declarations (generated TB/FM modules are split by their own set,
                  # NOT by the union: the same name `Pre` is statement-side in one copy and proof-side in another)
                  'names_by_module': {}}
    for (n_, mod_) in allc:
        layout_map['names_by_module'].setdefault(mod_, []).append(n_)
    for mod_ in layout_map['names_by_module']:
        layout_map['names_by_module'][mod_].sort()
    for m_ in list(spec_of):
        layout_map['old2proof'].setdefault(m_, proof_name(m_))
    json.dump(layout_map, open('scripts/layout-map.json', 'w'), indent=0, sort_keys=True)
    r = sh([sys.executable, 'scripts/gen-layout.py', 'regen', L])
    print(r.stdout.strip())
    if r.returncode != 0: sys.exit('gen-layout regen failed: %s' % (r.stdout + r.stderr)[-800:])
    patch_check_generated()
    update_whitelist(plan)
    git('add', '-A', 'lean')
    check_imports()
    print('restructure: done; now: scripts/check-spec-closure')


def filter_ctx(body, known_ns, known_consts):
    """in a Spec file keep `open`/`export` of Fv256 namespaces only when the spec modules provide them (the rest comes from proof modules)"""
    t = body.strip()
    m = re.match(r'^open\s+([^\n(]*?)\s*$', t)
    if m and 'hiding' not in t and 'renaming' not in t:
        toks = [x for x in m.group(1).split() if not x.startswith('Fv256') or x in known_ns]
        return ('open ' + ' '.join(toks) + '\n') if toks else ''
    m = re.match(r'^export\s+(Fv256[\w.]*)\s*\(([^)]*)\)\s*$', t)
    if m:
        names = [x for x in m.group(2).split() if '%s.%s' % (m.group(1), x) in known_consts]
        return ('export %s (%s)\n' % (m.group(1), ' '.join(names))) if names else ''
    return body


def check_imports():
    mods = set()
    for r, _, fs in os.walk(FV):
        for f in fs:
            if f.endswith('.lean'): mods.add(mod_of(os.path.join(r, f)))
    bad = []
    for r, _, fs in os.walk(L):
        if '.lake' in r: continue
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(r, f)
                for ln in open(p):
                    m = re.match(r'^\s*import\s+(Fv256[\w.]*)', ln)
                    if m and m.group(1) not in mods and m.group(1) != 'Fv256':
                        bad.append((p, m.group(1)))
    if bad:
        for b in bad[:20]: print('BAD IMPORT', *b)
        sys.exit('%d imports do not resolve' % len(bad))


def wire_checks():
    p = 'scripts/no-sorry.sh'
    t = open(p).read()
    if 'check-spec-closure' not in t:
        marker = '[ $fail = 0 ] && echo "no-sorry: OK"'
        assert marker in t
        t = t.replace(marker, '''# RELEASE: every final theorem statement depends only on lean/Fv256/Spec (Lean-computed closure; elaborates statements only, ~30 min).
# Needs build/harness-* and a janus binary (JANUS=... or build/janus); see scripts/check-spec-closure.
if [ -n "${RELEASE:-}" ] && [ -d lean/Fv256/Spec ]; then python3 scripts/check-spec-closure || fail=1; fi
''' + marker)
        open(p, 'w').write(t)
    p = 'scripts/verify-all.sh'
    t = open(p).read()
    if 'check-spec-closure' not in t:
        marker = 'mkdir -p build\n'
        assert marker in t
        t = t.replace(marker, marker + '# layout preflight: lean/Fv256 holds only Spec/ and Proofs/, and Spec/ never imports Proofs/ (the full closure check is `RELEASE=1 scripts/no-sorry.sh`)\n'
                      'python3 "$root/scripts/check-spec-closure" --structure-only || { echo "check-spec-closure --structure-only failed" >&2; exit 2; }\n', 1)
        open(p, 'w').write(t)


def patch_check_generated():
    p = 'scripts/check-generated.sh'
    t = open(p).read()
    if 'gen-layout.py' in t: return
    marker = 'fail=0\n'
    assert marker in t
    new = marker + '''# layout: after scripts/restructure.py the generators run unchanged on a LEGACY VIEW of the Spec/ + Proofs/ modules and their output is split back
# (scripts/gen-layout.py); the generated TB/FM modules live in lean/Fv256/{Spec,Proofs}/{Arm64,Amd64}/{TB,FM}.
if [ -d lean/Fv256/Proofs ] && [ -f scripts/layout-map.json ]; then
  for g in scripts/gen-*.sh; do b="$(basename "$g" .sh)"; case " $GEN_ORDER " in *" $b "*) ;; *) echo "check-generated: FAIL: $g is not listed in GEN_ORDER of scripts/check-generated.sh"; fail=1;; esac; done
  python3 scripts/gen-layout.py check --order "$GEN_ORDER" lean || fail=1
  [ $fail = 0 ] && echo "check-generated: OK (all $(echo $GEN_ORDER | wc -w) generators reproduce the committed modules, via the legacy view)"
  exit $fail
fi
'''
    open(p, 'w').write(t.replace(marker, new, 1))


def update_whitelist(plan):
    """scripts/tactic-whitelist.txt: paths and hashes of the moved files. Content differs only in the rewritten `import` lines (verified here)"""
    p = 'scripts/tactic-whitelist.txt'
    if not os.path.exists(p): return
    lines = open(p).read().split('\n'); out = []; rep_ = []
    for ln in lines:
        if not ln.strip() or ln.startswith('#'): out.append(ln); continue
        h, _, path = ln.partition('\t'); path = path.strip()
        mod = mod_of(path)
        if mod not in plan:
            out.append(ln); rep_.append('KEPT (not in plan) ' + path); continue
        newp = path_of(proof_name(mod))
        old = plan[mod]['text']; new = open(newp).read()
        strip_imp = lambda t: re.sub(r'(?m)^import .*\n', '', t)
        same = strip_imp(old).strip() == strip_imp(new).strip()
        import hashlib
        out.append('%s\t%s' % (hashlib.sha256(open(newp, 'rb').read()).hexdigest(), newp))
        rep_.append('%s %s -> %s' % ('IMPORT-LINES-ONLY' if same else 'CONTENT-CHANGED(split)', path, newp))
    open(p, 'w').write('\n'.join(out))
    json.dump(rep_, open('build/whitelist-moves.json', 'w'), indent=1)
    print('\n'.join(rep_))


def write_umbrella():
    """lean/Fv256/Spec.lean: imports every Spec module that does not (transitively) import Extracted, so `lake build` checks them."""
    imps = {}
    for r, _, fs in os.walk(FV + '/Spec'):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(r, f)
                imps[mod_of(p)] = re.findall(r'^import\s+(\S+)', open(p).read(), re.M)
    memo = {}
    def ext(m):
        if m == 'Extracted': return True
        if m not in imps: return False
        if m not in memo:
            memo[m] = False
            memo[m] = any(ext(i) for i in imps[m])
        return memo[m]
    free = sorted(m for m in imps if not ext(m))
    open(FV + '/Spec.lean', 'w').write('-- Umbrella of the SPECIFICATION modules that do not depend on an extraction (the others import `Extracted` and are\n'
        '-- elaborated together with their theorem by `janus verify`). Generated by scripts/restructure.py.\n' + ''.join('import %s\n' % m for m in free))
    print('umbrella Fv256.Spec: %d of %d spec modules' % (len(free), len(imps)))


# ---------------------------------------------------------------------------------------------------------------- scripts / docs


PATH_RULES = [
    (re.compile(r'(lean/Fv256|\$L/Fv256|\$\{L\}/Fv256|Fv256)/(Arm64|Amd64v3|Amd64)(?!\w)'), lambda m: '%s/Proofs/%s' % (m.group(1), m.group(2))),
    (re.compile(r'(lean/Fv256|\$L/Fv256|\$\{L\}/Fv256|\$snap/lean/Fv256)/(\$\{?(?:dir|D|isa|ISA|I)\}?)(?=/)'), lambda m: '%s/Proofs/%s' % (m.group(1), m.group(2))),
    (re.compile(r"lean/Fv256/%s/"), lambda m: 'lean/Fv256/Proofs/%s/'),
    (re.compile(r'lean/Fv256/\{Arm64,Amd64\}'), lambda m: 'lean/Fv256/Proofs/{Arm64,Amd64}'),
]


def rewrite_scripts(mapping):
    """textual rewrite of paths and `import Fv256...` lines in scripts, templates, tools and docs"""
    targets = []
    for d in ('scripts', 'tools'):
        for r, _, fs in os.walk(d):
            if '__pycache__' in r: continue
            for f in fs:
                targets.append(os.path.join(r, f))
    targets += [f for f in os.listdir('.') if f.endswith(('.md', '.sh', '.txt')) and os.path.isfile(f)]
    imp = re.compile(r'(\bimport\s+)(Fv256(?:\.[\w@]+)+)')
    n = 0
    for p in targets:
        if os.path.basename(p).startswith('gen-') or os.path.basename(p) in ('layout-map.json', 'tactic-whitelist.txt', 'check-generated.sh'): continue
        if p.endswith(('restructure.py', 'leansplit.py', 'spec_survey.py', 'check-spec-closure', 'SvyTools.lean')): continue
        try:
            t = open(p).read()
        except Exception:
            continue
        o = t
        for rx, fn in PATH_RULES:
            t = rx.sub(fn, t)
        def fi(m):
            mod = m.group(2)
            if mod not in mapping and re.match(r'Fv256\.(Arm64|Amd64|Amd64v3)\.', mod):
                return m.group(1) + proof_name(mod)
            return m.group(1) + mapping.get(mod, mod)
        t = imp.sub(fi, t)
        t = re.sub(r'(import Fv256\\\.)(Arm64|Amd64)(?=\\\.)', r'\1Proofs\\.\2', t)
        if t != o:
            open(p, 'w').write(t); n += 1
    print('rewrote %d script/doc files' % n)


if __name__ == '__main__':
    main()
