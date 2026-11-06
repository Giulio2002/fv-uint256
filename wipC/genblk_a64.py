#!/usr/bin/env python3
# usage: genblk_a64.py K < lean/Fv256/Arm64/MarshalSSZAppendG.lean > blkK.lean (K = 1, 2): arm64 block-K lemma from block 0
import sys
k = int(sys.argv[1])
t = sys.stdin.read()
stride = 0x4c
pcm = 0x24 + stride * k
pcn = 0x24 + stride * (k + 1)
pcr = 0x64 + stride * k
sp = 16 + 8 * k
t = t.replace('theorem blk0', 'theorem blk%d' % k)
t = t.replace('(hl0 : len.toNat = len0)', '(hl0 : len.toNat = len0 + %d)' % (8 * k))
t = t.replace('Extracted.entry + 0x70', 'Extracted.entry + @PCN@')
t = t.replace('Extracted.entry + 0x64', 'Extracted.entry + @PCR@')
t = t.replace('Extracted.entry + 0x24)', 'Extracted.entry + @PCM@)', 1)
t = t.replace('@PCN@', hex(pcn)).replace('@PCR@', hex(pcr)).replace('@PCM@', hex(pcm))
t = t.replace('s.sp.toNat - 16', 's.sp.toNat - %d' % sp)
t = t.replace('have hz8 : S.mem.readLE z.toNat 8 = s.mem.readLE z.toNat 8 := by simpa using hzs 0 (by omega)',
              'have hz8 : S.mem.readLE (z.toNat + %d) 8 = s.mem.readLE (z.toNat + %d) 8 := hzs %d (by omega)' % (8 * k, 8 * k, k))
t = t.replace('S.mem.readLE z.toNat 8', 'S.mem.readLE (z.toNat + %d) 8' % (8 * k))
t = t.replace('Memory.readLE S.mem z.toNat 8', 'Memory.readLE S.mem (z.toNat + %d) 8' % (8 * k))

HM1 = """      have hmid' : M.readLE (r0.toNat + len0) (len.toNat - len0) = S.mem.readLE (pp.toNat + len0) (len.toNat - len0) := by
        apply readLE_bytes_shift; intro i hi
        rw [show r0.toNat + len0 + i = r0.toNat + (len0 + i) by omega, hcopy (len0 + i) (by omega),
          Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega),
          show pp.toNat + (len0 + i) = pp.toNat + len0 + i by omega]
"""
TMPL = """      have h1 : len.toNat + 8 - len0 = (len.toNat - len0) + 8 := by omega
      have h2 : @X@.toNat + len.toNat = @X@.toNat + len0 + (len.toNat - len0) := by omega
      rw [@PRE@hlen8, h1, h2]
      exact mid_step @M@ s.mem (@X@.toNat + len0) (len.toNat - len0) z.toNat _ @HM@
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + @K8@ by omega]; exact hz8)
"""
OLD = {
 'pp': """      have e : pp.toNat + len0 = pp.toNat + len.toNat := by omega
      rw [hlen8, show len.toNat + 8 - len0 = 8 by omega, e, Memory.readLE_writeLE_self, hz8]
      exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
""",
 'r0': """      have e : r0.toNat + len0 = r0.toNat + len.toNat := by omega
      rw [e1, hlen8, show len.toNat + 8 - len0 = 8 by omega, e, Memory.readLE_writeLE_self, hz8]
      exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
"""}
for X in ('pp', 'r0'):
    old = OLD[X]
    assert old in t, X
    new = TMPL.replace('@X@', X).replace('@K8@', str(8 * k))
    if X == 'pp':
        new = new.replace('@PRE@', '').replace('@M@', 'S.mem').replace('@HM@', 'hmid')
    else:
        new = HM1 + new.replace('@PRE@', 'e1, ').replace('@M@', 'M').replace('@HM@', "(hmid'.trans hmid)")
    t = t.replace(old, new, 1)
sys.stdout.write(t)
