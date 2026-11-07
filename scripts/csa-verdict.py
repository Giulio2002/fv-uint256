#!/usr/bin/env python3
import sys,re
t=open(sys.argv[1],errors='replace').read(); mode=sys.argv[2]
errs=[l for l in t.splitlines() if re.search(r'error:|EXTRACT-FAIL',l)]
inv=re.findall(r'=== (\S+): FAILED ===\s*\nInvalid: (.*)',t)
bad=[(n,m) for n,m in inv if not re.search(r'depends on disallowed axioms: sorryAx',m)] if mode=='audit' else inv
if errs: print('VERDICT COMPILE-ERR'); print('\n'.join(errs[:8]))
elif bad: print('VERDICT REJECT'); [print(n,m[:900]) for n,m in bad[:6]]
elif re.search(r'\bValid\b|PASS|verified',t) or mode=='audit': print('VERDICT AUDIT-PASS' if mode=='audit' else 'VERDICT FULL-PASS')
else: print('VERDICT UNKNOWN')
