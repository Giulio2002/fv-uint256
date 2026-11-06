#!/usr/bin/env python3
# usage: gen.py K  -> prints block-K lemma from blk.tmpl
import sys
k = int(sys.argv[1])
pcm = [0x20, 0x63, 0xa7, 0xeb][k]
pcn = [0x63, 0xa7, 0xeb, 0][k]
pcr = [0x47, 0x8b, 0xcf, 0x113][k]
t = open('/srv/fv-uint256-wC/scratchC/blk.tmpl').read()
t = t.replace('@K@', str(8*k)).replace('@KI@', str(k)).replace('@PCM@', hex(pcm)).replace('@PCN@', hex(pcn)).replace('@PCR@', hex(pcr))
print(t)
