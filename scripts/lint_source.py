#!/usr/bin/env python3
"""scripts/lint_source.py -- second-layer SOURCE lints for lean/ (the Lean-level lint is scripts/check-lean-lint; both are run by RELEASE no-sorry).

1. Compile-time execution / hidden-content commands (token level, comment- and string-aware, word-boundary aware, independent of `open IO`):
   #eval, run_cmd, run_tac, run_elab, run_meta, #exit (truncates the file), initialize, builtin_initialize, @[init ..], @[builtin_init ..],
   unsafe, `lean_exe`/plugin/precompile settings in the lakefile.
2. Imports, parsed by Lean's own header parser (scripts/LintImports.lean, so `import A import B` on one line, `import all`, comment tricks and
   `prelude` are seen exactly as the compiler sees them): no `prelude`, no `import all`, no private/meta import, only Fv256 / Extracted / Janus / Lean / Std / Init.
Usage: scripts/lint_source.py [--imports-json OUT] ; exit 1 on any finding.
"""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
FORBID = [
    (r'#eval', 'compile-time #eval'), (r'run_cmd', 'compile-time run_cmd'), (r'run_tac', 'compile-time run_tac'),
    (r'run_elab', 'compile-time run_elab'), (r'run_meta', 'compile-time run_meta'), (r'#exit', '#exit (hides the rest of the file)'),
    (r'builtin_initialize', 'builtin_initialize'), (r'initialize', 'initialize'), (r'unsafe', 'unsafe'),
    (r'@\[\s*(?:[^\]]*,\s*)?(?:builtin_)?init\b', '@[init] attribute'), (r'@\[\s*(?:[^\]]*,\s*)?extern\b', '@[extern] attribute'),
    (r'@\[\s*(?:[^\]]*,\s*)?export\b', '@[export] attribute'),
]
ALLOWED_ROOTS = {'Fv256', 'Extracted', 'Janus', 'Lean', 'Std', 'Init'}


def strip(src):
    """blank out comments and string literals (keeping newlines so line numbers stay right)"""
    out = []; i = 0; n = len(src); depth = 0
    while i < n:
        if depth:
            if src.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
            if src.startswith('-/', i): depth -= 1; out.append('  '); i += 2; continue
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        if src.startswith('/-', i): depth = 1; out.append('  '); i += 2; continue
        if src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"': j += 2 if src[j] == '\\' else 1
            out.append(''.join('\n' if c == '\n' else ' ' for c in src[i:j + 1])); i = j + 1; continue
        if src[i] == "'" and i + 2 < n and (src[i + 2] == "'" or src[i + 1] == '\\'):
            out.append('   '); i += 3; continue
        out.append(src[i]); i += 1
    return ''.join(out)


def lean_files():
    fs = []
    for r, ds, f in os.walk('lean'):
        ds[:] = [d for d in ds if d != '.lake']
        fs += [os.path.join(r, x) for x in f if x.endswith('.lean')]
    return sorted(fs)


def parse_imports(files):
    res = {}
    for k in range(0, len(files), 400):
        chunk = [os.path.relpath(f, 'lean') for f in files[k:k + 400]]
        r = subprocess.run(['lean', '--run', os.path.join(ROOT, 'scripts/LintImports.lean')] + chunk, cwd='lean', capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit('lint_source: FAIL: header parse failed: ' + r.stderr[-500:])
        for ln in r.stdout.splitlines():
            f, m, fl = (ln.split('\t') + [''])[:3]
            res.setdefault('lean/' + f, []).append((m, fl))
    return res


def main():
    fail = 0
    files = lean_files()
    for f in files:
        s = strip(open(f, errors='ignore').read())
        for rx, why in FORBID:
            for m in re.finditer(r'(?<![\w.\'])' + rx + r'(?![\w\'!?])' if rx[0] != '@' else rx, s):
                line = s.count('\n', 0, m.start()) + 1
                print('FAIL: %s:%d: %s' % (f, line, why)); fail = 1; break
    lf = [x for x in ('lean/lakefile.toml', 'lean/lakefile.lean') if os.path.exists(x)]
    if os.path.exists('lean/lakefile.lean'):
        print('FAIL: lean/lakefile.lean exists (a Lean lakefile executes code at build time; use lakefile.toml)'); fail = 1
    t = re.sub(r'#[^\n]*', '', open('lean/lakefile.toml').read())
    for key in ('precompileModules', 'extraDepTargets', 'moreLeanArgs', 'weakLeanArgs', 'plugins', 'moreServerArgs', 'buildType', 'preferReleaseBuild', 'lean_exe', 'extern_lib', 'input_file', 'input_dir', 'post_update'):
        if re.search(r'\b' + key + r'\b', t):
            print('FAIL: lean/lakefile.toml uses `%s`' % key); fail = 1
    imps = parse_imports(files)
    for f in files:
        mods = imps.get(f, [])
        if not any(m == 'Init' and not fl for m, fl in mods):
            print('FAIL: %s: `prelude` (no implicit Init import)' % f); fail = 1
        for m, fl in mods:
            if fl and m != 'Init':
                print('FAIL: %s: `%s` imported with modifier `%s`' % (f, m, fl)); fail = 1
            if m.split('.')[0] not in ALLOWED_ROOTS:
                print('FAIL: %s: imports %s (outside Fv256/Extracted/Janus/Lean/Std/Init)' % (f, m)); fail = 1
    if len(sys.argv) > 2 and sys.argv[1] == '--imports-json':
        json.dump(imps, open(sys.argv[2], 'w'))
    print('lint_source: %d files; %s' % (len(files), 'FAILED' if fail else 'OK'))
    return fail


if __name__ == '__main__':
    sys.exit(main())
