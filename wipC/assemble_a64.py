#!/usr/bin/env python3
# Writes lean/Fv256/Arm64/MsaBlk{1,2,3}.lean (lemma-only modules importing MarshalSSZAppendG) from the generators.
import subprocess, sys
root = '/srv/fv-uint256-wC'
G = open(root + '/lean/Fv256/Arm64/MarshalSSZAppendG.lean').read()
hdr = '''import Fv256.Arm64.MarshalSSZAppendG

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa

namespace Fv256.Arm64.MarshalSSZAppendG

'''
def body(txt, name):
    i = txt.index('set_option maxRecDepth 20000 in\nset_option maxHeartbeats 0 in\ntheorem ' + name)
    return txt[i:]
for k in (1, 2):
    t = subprocess.run([sys.executable, root + '/wipC/genblk_a64.py', str(k)], input=G, capture_output=True, text=True).stdout
    open(root + '/lean/Fv256/Arm64/MsaBlk%d.lean' % k, 'w').write(hdr + body(t, 'blk%d' % k))
t = subprocess.run([sys.executable, root + '/wipC/genblk3f_a64.py'], input=G, capture_output=True, text=True).stdout
open(root + '/lean/Fv256/Arm64/MsaBlk3.lean', 'w').write(hdr + body(t, 'blk3f'))
