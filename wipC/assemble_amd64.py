#!/usr/bin/env python3
# Writes lean/Fv256/Amd64/MsaBlk{0,1,2,3}.lean from wipC/MsaBlk0.amd64.lean and the generators.
import subprocess, sys
root = '/srv/fv-uint256-wC'
base = open(root + '/wipC/MsaBlk0.amd64.lean').read().rstrip('\n')
if 'end Fv256.Amd64.Msa' not in base:
    base += '\n\nend Fv256.Amd64.Msa\n'
open(root + '/lean/Fv256/Amd64/MsaBlk0.lean', 'w').write(base)
hdr = '''import Fv256.Amd64.MsaBlk0

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

'''
def body(txt, name):
    i = txt.index('set_option maxRecDepth 20000 in\nset_option maxHeartbeats 0 in\ntheorem ' + name)
    return txt[i:]
def endfix(s):
    s = s.rstrip('\n')
    return s + ('\n' if s.endswith('end Fv256.Amd64.Msa') else '\n\nend Fv256.Amd64.Msa\n')
for k in (1, 2):
    t = subprocess.run([sys.executable, root + '/wipC/genblk.py', str(k)], input=base, capture_output=True, text=True).stdout
    open(root + '/lean/Fv256/Amd64/MsaBlk%d.lean' % k, 'w').write(hdr + endfix(body(t, 'blk%d' % k)))
t = subprocess.run([sys.executable, root + '/wipC/genblk3f.py'], input=base, capture_output=True, text=True).stdout
open(root + '/lean/Fv256/Amd64/MsaBlk3.lean', 'w').write(hdr + endfix(body(t, 'blk3f')))
