#!/usr/bin/env python3
"""Shift the address literals of the hex proofs from the pre-master binary to the master binary (one-off migration)."""
import re, sys
isa = sys.argv[1]
if isa == 'Arm64':
    ranges = [(0xb5b40, 0xb5b40 + 0x1d0 + 0x1000, 80),          # code (all hex functions)
              (1001813, 1001813 + 256, 976),                     # hex table
              (1792752, 1792752 + 96, 32)]                       # error variables
else:
    ranges = [(0x4b1b40, 0x4b1d60 + 0x1c0, 96),
              (5175774, 5175774 + 256, 1008),
              (0x4cbe00, 0x4cbe00 + 256, 384),
              (5987120, 5987120 + 96, 8224)]
def shift(n):
    for lo, hi, d in ranges:
        if lo <= n <= hi: return n + d
    return n
def rep_dec(m):
    n = int(m.group(0)); return str(shift(n))
def rep_hex(m):
    t = m.group(0); n = int(t, 16); r = shift(n)
    return t if r == n else '0x%x' % r
for p in sys.argv[2:]:
    s = open(p).read()
    s2 = re.sub(r'(?<![\w.])0x[0-9a-fA-F]{5,}(?![\w])', rep_hex, s)
    s2 = re.sub(r'(?<![\w.#])\d{6,}(?![\w])', rep_dec, s2)
    if s2 != s: open(p, 'w').write(s2); print('shifted', p)
