#!/usr/bin/env python3
"""gen_exp_loops.py : derive arm64 ExpLoop2..4 from the hand-written ExpLoop1.lean (loop head offsets, bit limits, register of the word)."""
import re, sys
d = '/srv/fv-uint256-wh/lean/Fv256/Proofs/Arm64/'
src = open(d + 'ExpLoop1.lean').read()
for j, head, lim in ((2, 0x194, 128), (3, 0x1f0, 192), (4, 0x248, 256)):
    s = src
    s = s.replace('ExpLoop1', 'ExpLoop%d' % j).replace('Inv1', 'Inv%d' % j).replace('head1', 'head%d' % j).replace('loop1', 'loop%d' % j)
    s = s.replace('expEntry + 0x118', 'expEntry + 0x%x' % head)
    s = s.replace('min n 64', 'min n %d' % lim).replace('k ≤ 64', 'k ≤ %d' % lim).replace('k < 64', 'k < %d' % lim).replace('¬64 ≤', '¬%d ≤' % lim)
    s = s.replace('S.regs 4 = BitVec.ofNat 64 base0 ∧ S.regs 5 = BitVec.ofNat 64 w ∧', 'S.regs 4 = BitVec.ofNat 64 w ∧')
    s = s.replace('r4, r5, r18', 'r4, r18')
    s = s.replace('r3, r4, r5, r18', 'r3, r4, r18')
    s = s.replace('r0, r1, r2, r3, r4, r5, r18, r28, r29', 'r0, r1, r2, r3, r4, r18, r28, r29')
    s = s.replace('      · rw [d144, mb0]\n', '')
    s = s.replace('      · exact Fv256.Arm64.ExpLoopLem.lsr1 w hw\n', '      · exact Fv256.Arm64.ExpLoopLem.lsr1 w hw\n')
    if j == 4:
        s = s.replace(' S.regs 2 = BitVec.ofNat 64 ep ∧', '')
        s = s.replace('r0, r1, r2, r3,', 'r0, r1, r3,').replace('r0, r1, r2, r3, r4, r18', 'r0, r1, r3, r4, r18')
        s = s.replace('      · rw [d184, mep]\n', '')
    q25 = ', '.join(['?_'] * 25); q = ', '.join(['?_'] * (23 if j == 4 else 24))
    s = s.replace(q25, q)
    open(d + 'ExpLoop%d.lean' % j, 'w').write(s)
