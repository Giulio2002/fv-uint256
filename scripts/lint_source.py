#!/usr/bin/env python3
"""scripts/lint_source.py -- second-layer SOURCE lints for lean/ (the Lean-level lint is scripts/check-lean-lint; both are run by RELEASE no-sorry).

1. Compile-time execution / hidden-content commands (token level, comment- and string-aware, word-boundary aware, independent of `open IO`):
   #eval, run_cmd, run_tac, run_elab, run_meta, #exit (truncates the file), initialize, builtin_initialize, @[init ..], @[builtin_init ..],
   unsafe, `lean_exe`/plugin/precompile settings in the lakefile.
2. Imports, parsed by Lean's own header parser (scripts/LintImports.lean, so `import A import B` on one line, `import all`, comment tricks and
   `prelude` are seen exactly as the compiler sees them): no `prelude`, no `import all`, no private/meta import, only Fv256 / Extracted / Janus / Lean / Std / Init.
3. Metaprogramming (N13 LA1): `elab`, `macro`, `macro_rules`, `syntax`, `elab_rules`, `declare_syntax_cat`, `simproc`/`dsimproc`/`simproc_decl`, `register_*`,
   `binder_predicate`, and any attribute (`@[..]` / `attribute [..]`) other than the allowlisted proof attributes (simp, reducible, irreducible,
   match_pattern, localsimp) -- e.g. `@[command_elab]`, `@[term_elab]`, `@[tactic]`, `@[macro]` -- are rejected in every lean/**/*.lean file
   EXCEPT the files listed in scripts/tactic-whitelist.txt (`sha256<TAB>path`, the files that legitimately define tactics).  A whitelisted
   file must still contain such a construct and (under RELEASE=1; a warning otherwise) must hash to the listed sha256, so it cannot change
   without the whitelist being updated in the same reviewed commit.  `initialize`/`builtin_initialize`/`@[init]`/`attribute [init ..]` are never
   whitelistable.  Lean-level counterpart: `#lint_io` rejects any Fv256 declaration whose value references runParserCategory / elabCommand / evalTerm /
   evalExpr / evalConst / IO.* / System.* ... (scripts/SvyTools.lean).
4. Hidden modules (N13 LA2): lean/lakefile.toml may declare only the known package (one `lean_lib` Fv256 with no srcDir/roots/globs/..., one `require`
   janus from the pinned git); symlinks under lean/ are rejected (Lake follows them); the compile-time-command token lint (1) also runs over EVERY other
   .lean file in the repo (except .git, .lake, build/ and the regression fixtures scripts/lint-tests/).
Usage: scripts/lint_source.py [--imports-json OUT] [--update-whitelist] ; exit 1 on any finding.
"""
import hashlib, json, os, re, subprocess, sys
try:
    import tomllib
except ImportError:  # pragma: no cover
    tomllib = None

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
FORBID = [
    (r'#eval', 'compile-time #eval'), (r'run_cmd', 'compile-time run_cmd'), (r'run_tac', 'compile-time run_tac'),
    (r'run_elab', 'compile-time run_elab'), (r'run_meta', 'compile-time run_meta'), (r'#exit', '#exit (hides the rest of the file)'),
    (r'builtin_initialize', 'builtin_initialize'), (r'initialize', 'initialize'), (r'unsafe', 'unsafe'),
    (r'@\[\s*(?:[^\]]*,\s*)?(?:builtin_)?init\b', '@[init] attribute'), (r'@\[\s*(?:[^\]]*,\s*)?extern\b', '@[extern] attribute'),
    (r'@\[\s*(?:[^\]]*,\s*)?export\b', '@[export] attribute'),
]
# metaprogramming constructs: only in whitelisted files (scripts/tactic-whitelist.txt)
META_KW = ['elab', 'macro', 'macro_rules', 'syntax', 'elab_rules', 'declare_syntax_cat', 'simproc', 'dsimproc', 'simproc_decl', 'binder_predicate',
           'register_simp_attr', 'register_option', 'register_builtin_option', 'register_label_attr', 'register_parser_alias', 'register_tactic_tag',
           'register_error_explanation', 'register_derive_handler']
META_RX = re.compile(r'(?<![\w.\'])(' + '|'.join(META_KW) + r')(?![\w\'!?])')
ATTR_OK = {'simp', 'reducible', 'irreducible', 'match_pattern', 'localsimp'}
ATTR_HARD = {'init', 'builtin_init', 'extern', 'export', 'implemented_by', 'csimp', 'never_extract', 'run_cmd'}
WHITELIST = 'scripts/tactic-whitelist.txt'
ALLOWED_LAKE_REQUIRE = {'janus'}
ALLOWED_LAKE_TOP = {'name', 'defaultTargets', 'require', 'lean_lib'}
ALLOWED_LAKE_REQ = {'name', 'git', 'rev'}
ALLOWED_LAKE_LIB = {'name'}
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


def attributes(src):
    """(kind, name, offset) for every attribute item in `@[...]` and `attribute [...]` of comment/string-stripped source"""
    res = []
    for m in re.finditer(r'@\[|(?<![\w.\'])attribute\s*\[', src):
        i = m.end(); depth = 1; j = i; items = []; cur = i
        while j < len(src) and depth:
            c = src[j]
            if c in '[(': depth += 1
            elif c in '])': depth -= 1
            elif c == ',' and depth == 1: items.append(src[cur:j]); cur = j + 1
            j += 1
        items.append(src[cur:j - 1])
        for it in items:
            toks = re.findall(r"[^\s,]+", it)
            while toks and toks[0] in ('local', 'scoped', '-', '←'): toks = toks[1:]
            if toks and toks[0].startswith('-'): toks[0] = toks[0][1:]
            res.append((m.group(0).strip(), toks[0] if toks else '', m.start()))
    return res


def sha256(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def load_whitelist():
    wl = {}
    if not os.path.exists(WHITELIST):
        return wl
    for ln in open(WHITELIST).read().splitlines():
        if not ln.strip() or ln.startswith('#'): continue
        h, _, p = ln.partition('\t')
        wl[p.strip()] = h.strip()
    return wl


def meta_hits(src):
    """metaprogramming constructs in stripped source: [(line, what)]"""
    hits = [(src.count('\n', 0, m.start()) + 1, m.group(1)) for m in META_RX.finditer(src)]
    for kind, name, off in attributes(src):
        if name not in ATTR_OK and name not in ATTR_HARD:
            hits.append((src.count('\n', 0, off) + 1, '%s attribute `%s`' % (kind, name)))
    return hits


def lake_checks():
    """lean/lakefile.toml may declare only the known package (N13 LA2: srcDir/roots/globs hide modules from the lints)"""
    fail = 0
    raw = open('lean/lakefile.toml').read()
    if tomllib is None:
        print('FAIL: python tomllib unavailable (need python >= 3.11 for the lakefile structure check)'); return 1
    try:
        t = tomllib.loads(raw)
    except Exception as e:
        print('FAIL: lean/lakefile.toml does not parse: %s' % e); return 1
    for k in t:
        if k not in ALLOWED_LAKE_TOP: print('FAIL: lean/lakefile.toml: top-level key `%s` not allowed' % k); fail = 1
    reqs = t.get('require', [])
    for r in reqs:
        for k in r:
            if k not in ALLOWED_LAKE_REQ: print('FAIL: lean/lakefile.toml: [[require]] key `%s` not allowed' % k); fail = 1
        if r.get('name') not in ALLOWED_LAKE_REQUIRE: print('FAIL: lean/lakefile.toml: require `%s` not allowed' % r.get('name')); fail = 1
    libs = t.get('lean_lib', [])
    if [l.get('name') for l in libs] != ['Fv256']:
        print('FAIL: lean/lakefile.toml: lean_lib set must be exactly [Fv256], got %s' % [l.get('name') for l in libs]); fail = 1
    for l in libs:
        for k in l:
            if k not in ALLOWED_LAKE_LIB: print('FAIL: lean/lakefile.toml: lean_lib key `%s` not allowed (srcDir/roots/globs hide modules from the lints)' % k); fail = 1
    if t.get('defaultTargets', ['Fv256']) != ['Fv256']: print('FAIL: lean/lakefile.toml: defaultTargets must be ["Fv256"]'); fail = 1
    if re.search(r'\b(srcDir|roots|globs|libPrefixName|libName|nativeFacets|moreLinkArgs|dynlibs|path)\b', re.sub(r'#[^\n]*', '', raw)):
        print('FAIL: lean/lakefile.toml mentions srcDir/roots/globs/path/...'); fail = 1
    if os.path.exists('lean/lake-manifest.json'):
        for p in json.load(open('lean/lake-manifest.json')).get('packages', []):
            if p.get('name') not in ALLOWED_LAKE_REQUIRE: print('FAIL: lean/lake-manifest.json: package `%s` not allowed' % p.get('name')); fail = 1
    return fail


def symlinks():
    res = []
    for r, ds, fs in os.walk('lean'):
        if r == 'lean': ds[:] = [d for d in ds if d != '.lake']
        for x in ds + fs:
            if os.path.islink(os.path.join(r, x)): res.append(os.path.join(r, x))
    return res


def other_lean_files():
    fs = []
    for r, ds, f in os.walk('.'):
        ds[:] = [d for d in ds if d not in ('.git', '.lake', 'build') and os.path.join(r, d) not in ('./lean', './scripts/lint-tests')]
        fs += [os.path.join(r, x)[2:] for x in f if x.endswith('.lean')]
    return sorted(fs)


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
    wl = load_whitelist(); release = bool(os.environ.get('RELEASE')); metafiles = {}
    if len(sys.argv) > 1 and sys.argv[1] == '--update-whitelist':
        for f in files:
            if meta_hits(strip(open(f, errors='ignore').read())): metafiles[f] = sha256(f)
        with open(WHITELIST, 'w') as o:
            o.write('# files that legitimately define tactics / syntax (scripts/lint_source.py, N13 LA1). Format: sha256<TAB>path.  Regenerate with\n'
                    '# scripts/lint_source.py --update-whitelist AFTER reviewing the diff of every changed file; RELEASE no-sorry fails on any hash mismatch.\n')
            for f in sorted(metafiles): o.write('%s\t%s\n' % (metafiles[f], f))
        print('wrote %s (%d files)' % (WHITELIST, len(metafiles))); return 0
    for l in symlinks(): print('FAIL: symlink %s under lean/ (Lake follows symlinks; modules behind it escape the lints)' % l); fail = 1
    fail |= lake_checks()
    for f in other_lean_files():
        s = strip(open(f, errors='ignore').read())
        for rx, why in FORBID:
            for m in re.finditer(r'(?<![\w.\'])' + rx + r'(?![\w\'!?])' if rx[0] != '@' else rx, s):
                print('FAIL: %s:%d: %s (outside lean/: every .lean in the repo is linted)' % (f, s.count('\n', 0, m.start()) + 1, why)); fail = 1; break
    for f in files:
        s = strip(open(f, errors='ignore').read())
        for kind, name, off in attributes(s):
            if name in ATTR_HARD:
                print('FAIL: %s:%d: %s attribute `%s`' % (f, s.count('\n', 0, off) + 1, kind, name)); fail = 1
        mh = meta_hits(s)
        if mh: metafiles[f] = mh
        if mh and f not in wl:
            print('FAIL: %s:%d: metaprogramming `%s` in a file not listed in %s (%d construct(s))' % (f, mh[0][0], mh[0][1], WHITELIST, len(mh))); fail = 1
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
    for f, h in sorted(wl.items()):
        msg = None
        if not os.path.exists(f): msg = 'whitelisted file is missing'
        elif not f.startswith('lean/'): msg = 'whitelist entry outside lean/'
        elif f not in metafiles: msg = 'whitelisted but contains no metaprogramming any more (remove it)'
        elif sha256(f) != h: msg = 'content changed since whitelisted (review, then scripts/lint_source.py --update-whitelist)'
        if msg:
            if release or msg.startswith(('whitelisted file is missing', 'whitelist entry')):
                print('FAIL: %s: %s' % (f, msg)); fail = 1
            else: print('WARN: %s: %s (fails under RELEASE=1)' % (f, msg))
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
