#!/usr/bin/env python3
"""scripts/spec_survey.py -- compute the SPEC CLOSURE of the final theorems, using Lean itself.

For every function row that verify-all.sh verifies (docs/COVERAGE.md status verified*/partial*, plus lean/Fv256/**/Amd64v3/*.lean) the
final theorem module is elaborated with the `SvyTools` elaborator (build/spec-ws/tools): every `theorem` body is replaced by `sorry`
(statements are fully elaborated, so the survey needs seconds per function, not the proof time), then `#spec_closure` collects the
Fv256 constants reachable from the TYPES of `correctness` and of every existential witness theorem (scripts/witness-theorems.py),
transitively through definitions (types and values; theorem values are never entered).  Janus.* / Extracted.* / core are excluded.

usage: scripts/spec_survey.py --out result.json [--isa arm64|amd64|amd64v3] [FN ...]
env:   SPEC_WS (workspace, default build/spec-ws), JANUS (janus binary for `janus extract`, default build/janus or PATH),
       SPEC_JANUS_PKG (the janus lake package, default lean/.lake/packages/janus), HEAVY=1 (wrap each lean in heavy-run), MEMCAP (12G)
"""
import argparse, hashlib, json, os, re, shutil, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
SCRIPTS = os.path.join(ROOT, 'scripts')


def sh(cmd, **kw):
    return subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True, **kw)


def layout_dir():
    """Directory holding the ISA proof dirs: lean/Fv256/Proofs after restructure, lean/Fv256 before."""
    return 'lean/Fv256/Proofs' if os.path.isdir('lean/Fv256/Proofs') else 'lean/Fv256'


def tasks(only, isas):
    rows = [l for l in open('docs/COVERAGE.md').read().splitlines() if l.startswith('| `')]
    out = []
    for row in rows:
        c = [x.strip() for x in row.split('|')]
        sym = c[1].strip('`')
        fn = sym.rsplit('.', 1)[-1]
        if only and fn not in only:
            continue
        for isa, st in (('arm64', c[3].replace(' ', '')), ('amd64', c[4].replace(' ', ''))):
            if isas and isa not in isas:
                continue
            if st.startswith(('verified', 'partial')):
                out.append((isa, fn, sym))
    if not isas or 'amd64v3' in isas:
        for f in sorted(os.listdir(os.path.join(layout_dir(), 'Amd64v3'))):
            fn = f[:-5]
            if f.endswith('.lean') and (not only or fn in only):
                out.append(('amd64v3', fn, fn))
    return out


def contract_flags(fn):
    r = sh(['bash', '-c', '. scripts/contract-flags.sh; contract_flags "$1"', 'x', fn])
    return r.stdout.split()


def prepare_ws(ws, pkg):
    """(Re)create the survey workspace: lakefile, SvyTools, a copy of lean/Fv256 with `import SvyTools` injected."""
    os.makedirs(ws + '/tools', exist_ok=True); os.makedirs(ws + '/ex', exist_ok=True); os.makedirs(ws + '/src', exist_ok=True)
    shutil.copy('lean/lean-toolchain', ws + '/lean-toolchain')
    if not os.path.lexists(ws + '/janus-pkg'):
        os.symlink(os.path.abspath(pkg), ws + '/janus-pkg')
    open(ws + '/lakefile.toml', 'w').write(
        'name = "svy"\ndefaultTargets = []\n\n[[require]]\nname = "janus"\npath = "janus-pkg"\n\n'
        '[[lean_lib]]\nname = "SvyTools"\nsrcDir = "tools"\n\n[[lean_lib]]\nname = "Extracted"\nsrcDir = "ex"\n\n'
        '[[lean_lib]]\nname = "Fv256"\nsrcDir = "src"\n')
    shutil.copy(os.path.join(SCRIPTS, 'SvyTools.lean'), ws + '/tools/SvyTools.lean')
    want = set()
    for r, _, fs in os.walk('lean/Fv256'):
        for f in fs:
            if not f.endswith('.lean'):
                continue
            p = os.path.join(r, f); q = os.path.join(ws, 'src', os.path.relpath(p, 'lean'))
            want.add(q)
            t = open(p).read()
            m = re.search(r'^import ', t, re.M)
            t = (t[:m.start()] + 'import SvyTools ' + t[m.start():]) if m else 'import SvyTools\n' + t
            os.makedirs(os.path.dirname(q), exist_ok=True)
            if not os.path.exists(q) or open(q).read() != t:
                open(q, 'w').write(t)
    shutil.copy('lean/Fv256.lean', ws + '/src/Fv256.lean')
    for r, _, fs in os.walk(ws + '/src'):      # stale copies from an earlier layout
        for f in fs:
            p = os.path.join(r, f)
            if f.endswith('.lean') and p not in want and p != ws + '/src/Fv256.lean':
                os.remove(p)


def run_lean(ws, argv, timeout):
    mc = os.environ.get('MEMCAP', '12G')
    cmd = ['memcap', '-m', mc] + argv
    if os.environ.get('HEAVY') == '1' and os.path.exists('/srv/janus-ops/bin/heavy-run'):
        cmd = ['/srv/janus-ops/bin/heavy-run', '--'] + ['timeout', str(timeout)] + cmd
    else:
        cmd = ['timeout', str(timeout)] + cmd
    env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('LEAN_NUM_THREADS', '8'))
    return subprocess.run(cmd, cwd=ws, capture_output=True, text=True, env=env)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--isa', action='append')
    ap.add_argument('fns', nargs='*')
    a = ap.parse_args()
    ws = os.path.abspath(os.environ.get('SPEC_WS', 'build/spec-ws'))
    pkg = os.environ.get('SPEC_JANUS_PKG', 'lean/.lake/packages/janus')
    janus = os.environ.get('JANUS') or (os.path.abspath('build/janus') if os.path.exists('build/janus') else 'janus')
    # (no in-place regeneration of the TB/FM modules here: a check script never rewrites tracked proof sources; scripts/check-generated.sh fails on drift)
    prepare_ws(ws, pkg)
    ld = layout_dir()
    res = {}
    for isa, fn, sym in tasks(set(a.fns), set(a.isa or [])):
        t0 = time.time()
        key = f'{isa}-{fn}'
        d = {'Arm64': 'Arm64', 'amd64': 'Amd64', 'arm64': 'Arm64', 'amd64v3': 'Amd64v3'}[isa]
        if isa == 'amd64v3':
            pf = fn; harness = 'build/harness-amd64v3'; flags = []; full = f'github.com/holiman/uint256.(*Int).{fn}'
        else:
            pf = fn
            mf = f'{ld}/{d}/{fn}Main.lean'
            if os.path.isfile(mf) and 'theorem correctness' in open(mf).read():
                pf = fn + 'Main'
            harness = f'build/harness-{isa}'
            full = (f'github.com/holiman/uint256.(*Int).{fn}' if sym.startswith('(*uint256.Int).') else f'github.com/holiman/uint256.{fn}')
            flags = contract_flags(fn)
        f = f'{ld}/{d}/{pf}.lean'
        # claim-file rows: lean/Fv256/<Isa>/<Fn>.lean holds `Fv256.<Isa>.<Fn>.correctness` and the Witness theorems
        cf = f'lean/Fv256/{d}/{fn}.lean'
        claim = os.path.isfile(cf) and re.search(r'^theorem correctness', open(cf).read(), re.M)
        if claim:
            f = cf; pf = fn
        if not os.path.isfile(f):
            res[key] = {'error': f'missing {f}'}; print(key, 'MISSING', f, flush=True); continue
        ex = f'{ws}/exout/{key}'
        shutil.rmtree(ex, ignore_errors=True)
        r = sh([janus, 'extract', harness, full, ex] + flags)
        if r.returncode != 0:
            res[key] = {'error': 'extract failed: ' + (r.stdout + r.stderr)[-300:]}; print(key, 'EXTRACT FAIL', flush=True); continue
        new = open(ex + '/Extracted.lean').read()
        cur = ws + '/ex/Extracted.lean'
        if not os.path.exists(cur) or open(cur).read() != new:
            open(cur, 'w').write(new)
        src = open(f).read()
        imports = [m for m in re.findall(r'^import (\S+)', src, re.M)]
        wit = [w for w in sh(['python3', os.path.join(SCRIPTS, 'witness-theorems.py'), f]).stdout.split() if w]
        roots = [f'Fv256.{d}.{pf}.correctness'] + wit
        q = open(os.path.join(ws, 'src', os.path.relpath(f, 'lean'))).read() + '\n#spec_closure ' + ' '.join(roots) + '\n#lint_io\n'
        qf = f'{ws}/q-{key}.lean'
        open(qf, 'w').write(q)
        deps = ['Extracted'] + [m for m in imports if m.startswith('Fv256')]
        b = run_lean(ws, ['lake', 'build'] + deps, 3600)
        if b.returncode != 0:
            el = [l for l in (b.stdout + b.stderr).splitlines() if l.startswith('error:') or ': error' in l]
            res[key] = {'error': 'lake build failed: ' + ' | '.join(el[:12])[:1800]}; print(key, 'BUILD FAIL', flush=True); continue
        o = run_lean(ws, ['lake', 'env', 'lean', qf], 3600)
        txt = o.stdout
        consts = []; rr = []
        for l in txt.splitlines():
            if l.startswith('@@S '):
                rr.append(l[4:].strip())
            elif l.startswith('@@C '):
                p = l[4:].split(' ')
                consts.append({'name': p[0], 'module': p[1] if p[1] != '<cur>' else f'Fv256.{d}.{pf}', 'kind': p[2], 'parent': p[3], 'range': p[4]})
        stm = {}
        for l in txt.splitlines():
            if l.startswith('@@T '):
                nm, _, body = l[4:].partition(' ')
                stm[nm] = hashlib.sha256(body.encode()).hexdigest()
        iol = sorted({l[5:].strip() for l in txt.splitlines() if l.startswith('@@IO ')})
        iocount = [l for l in txt.splitlines() if l.startswith('@@IOCOUNT ')]
        if not iocount:
            res[key] = {'error': '#lint_io did not run: ' + txt[-500:] + o.stderr[-300:]}; print(key, 'IOLINT MISSING', flush=True); continue
        if set(rr) != set(roots):
            res[key] = {'error': 'closure query failed: ' + txt[-800:] + o.stderr[-300:]}; print(key, 'QUERY FAIL', flush=True); continue
        errs = [l for l in txt.splitlines() if ': error:' in l]
        res[key] = {'file': f, 'roots': roots, 'consts': consts, 'errors': errs[:5], 'iolint': iol, 'stmt': stm}
        print(f'{key}: {len(consts)} consts, {len(wit)} witnesses, {time.time()-t0:.0f}s' + (f' ERRORS {errs[:1]}' if errs else ''), flush=True)
        os.remove(qf)
    json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
