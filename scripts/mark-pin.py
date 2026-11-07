#!/usr/bin/env python3
"""scripts/mark-pin.py PIN < verify-all-summary   : record 'verified-on' in COVERAGE.md for every 'ISA Fn PASS' line.
Usage: scripts/verify-all.sh Fn... | python3 scripts/mark-pin.py 77fb30cc   (reads lines like 'arm64    Add    PASS')"""
import re, sys
pin = sys.argv[1]
res = {}
for ln in sys.stdin:
    m = re.match(r'^(arm64|amd64)\s+(\S+)\s+(PASS|FAIL\S*|MISSING.*)\s*$', ln)
    if m: res[(m.group(2), m.group(1))] = m.group(3)
L = open('COVERAGE.md').read().split('\n')
for i, l in enumerate(L):
    if not l.startswith('| `'): continue
    c = l.split('|')
    fn = c[1].strip().strip('`').split('.')[-1]
    cell = c[-2].strip()
    parts = {p.split()[0]: p for p in cell.split(' / ') if p.split()[0] in ('arm64', 'amd64')}
    ch = False
    for isa in ('arm64', 'amd64'):
        if (fn, isa) in res and isa in parts:
            parts[isa] = '%s %s' % (isa, pin if res[(fn, isa)] == 'PASS' else 'FAIL(%s)' % pin); ch = True
    if ch:
        c[-2] = ' ' + ' / '.join(parts[k] for k in ('arm64', 'amd64') if k in parts) + ' '
        L[i] = '|'.join(c)
open('COVERAGE.md', 'w').write('\n'.join(L))
