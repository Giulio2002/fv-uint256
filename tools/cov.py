#!/usr/bin/env python3 -I
# cov.py Fn...  : mark COVERAGE.md rows from the build/log-<isa>-<Fn> verdicts (Verified on first line)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys, re
p=ROOT+'/COVERAGE.md'
s=open(p).read()
for fn in sys.argv[1:]:
    st={}
    for isa in ('arm64','amd64'):
        try: st[isa]=open((ROOT+f'/build/log-{isa}-{fn}')).readline().startswith('Verified')
        except OSError: st[isa]=False
    pat=re.compile(r'(\| `\(\*uint256\.Int\)\.%s` \|[^|]*\| )([^|]*)\|([^|]*)\|([^\n]*)'%re.escape(fn))
    m=pat.search(s)
    if not m: print('no row',fn); continue
    a='verified' if st['arm64'] else m.group(2).strip()
    b='verified' if st['amd64'] else m.group(3).strip()
    note=m.group(4) if (m.group(4).strip() not in ('','|')) else ' lean/Fv256/Proofs/{Arm64,Amd64}/%s.lean |'%fn
    s=s[:m.start()]+m.group(1)+a+' | '+b+' |'+note+s[m.end():]
open(p,'w').write(s)
