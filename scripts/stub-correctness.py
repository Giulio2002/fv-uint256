#!/usr/bin/env python3
"""scripts/stub-correctness.py FILE...  : (scratch trees only!) replace the proof of every `theorem correctness` by `sorry`, so that a
witness-statement/audit check does not recompile the heavy proofs.  Never run in the real worktree."""
import re, sys, importlib.util, os
spec = importlib.util.spec_from_file_location('u', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'upgrade-witness-run.py'))
u = importlib.util.module_from_spec(spec); spec.loader.exec_module(u)
for f in sys.argv[1:]:
    src = open(f).read(); cs = u.strip_comments(src)
    out = src
    for ns, kind, name, st, en in sorted([d for d in u.decls(cs) if d[2] == 'correctness'], reverse=True):
        t = cs[st:en]; a = u.top_assign(t)
        if a < 0: continue
        code_end = st + len(t.rstrip())
        out = out[:st + a + 2] + ' by sorry' + out[code_end:]
    open(f, 'w').write(out)
