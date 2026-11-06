#!/usr/bin/env python3
# usage: genblk.py K < MsaBlk0.amd64.lean > blkK.lean   (K = 1, 2): block-K lemma from the verified block-0 text
import sys
k = int(sys.argv[1])
t = sys.stdin.read()
pcm = [0x20, 0x63, 0xa7, 0xeb][k]
pcn = [0x63, 0xa7, 0xeb, 0x12f][k]
pcr = [0x47, 0x8b, 0xcf, 0x113][k]
ret = [4926695, 4926763, 4926831, 4926899][k]
sp = 16 + 8 * k
t = t.replace('theorem blk0', 'theorem blk%d' % k)
t = t.replace('hl0 : len.toNat = len0 + 0', 'hl0 : len.toNat = len0 + %d' % (8 * k))
t = t.replace('Extracted.entry + 0x63', 'Extracted.entry + @PCN@')
t = t.replace('Extracted.entry + 0x47', 'Extracted.entry + @PCR@')
t = t.replace('Extracted.entry + 0x20)', 'Extracted.entry + @PCM@)', 1)
t = t.replace('@PCN@', hex(pcn)).replace('@PCR@', hex(pcr)).replace('@PCM@', hex(pcm))
t = t.replace('4926695', str(ret))
t = t.replace('(s.regs 4).toNat - 16', '(s.regs 4).toNat - %d' % sp)
t = t.replace('hz8 : S.mem.readLE (z.toNat + 0) 8 = s.mem.readLE (z.toNat + 0) 8 := hzs (0)',
              'hz8 : S.mem.readLE (z.toNat + %d) 8 = s.mem.readLE (z.toNat + %d) 8 := hzs (%d)' % (8 * k, 8 * k, k))
# the limb loaded and stored is limb k
t = t.replace('S.mem.readLE z.toNat 8', 'S.mem.readLE (z.toNat + %d) 8' % (8 * k))
t = t.replace('Memory.readLE S.mem z.toNat 8', 'Memory.readLE S.mem (z.toNat + %d) 8' % (8 * k))

HM1 = """      have hmid' : M.readLE (r0.toNat + len0) (len.toNat - len0) = S.mem.readLE (pp.toNat + len0) (len.toNat - len0) := by
        apply readLE_bytes_shift; intro i hi
        rw [show r0.toNat + len0 + i = r0.toNat + (len0 + i) by omega, hcopy (len0 + i) (by omega),
          Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega), Memory.bytes_writeLE_outside _ (by unfold Apart at hdj; omega),
          show pp.toNat + (len0 + i) = pp.toNat + len0 + i by omega]
"""
TMPL = """      have h1 : len.toNat + 8 - len0 = (len.toNat - len0) + 8 := by omega
      have h2 : @X@.toNat + len.toNat = @X@.toNat + len0 + (len.toNat - len0) := by omega
      rw [hlen8, h1, h2]
      exact mid_step @M@ s.mem (@X@.toNat + len0) (len.toNat - len0) z.toNat _ @HM@
        (by rw [Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _), show z.toNat + (len.toNat - len0) = z.toNat + @K8@ by omega])
"""
OLD = """      have e : @X@.toNat + len0 = @X@.toNat + len.toNat := by omega
      simp only [Nat.add_zero] at hz8
      rw [hlen8, show len.toNat + 8 - len0 = 8 by omega, e, Memory.readLE_writeLE_self, hz8]
      exact Nat.mod_eq_of_lt (Memory.readLE_lt _ _ _)
"""
for X in ('pp', 'r0'):
    old = OLD.replace('@X@', X)
    assert old in t, X
    new = TMPL.replace('@X@', X).replace('@K8@', str(8 * k))
    if X == 'pp':
        new = new.replace('@M@', 'S.mem').replace('@HM@', 'hmid')
    else:
        new = HM1 + new.replace('@M@', 'M').replace('@HM@', "(hmid'.trans hmid)")
    t = t.replace(old, new, 1)
if k > 0:
    key = '    have hgC : ((S.mem.writeLE ((s.regs 4).toNat - %d) 8 (S.mem.readLE (z.toNat + %d) 8))' % (sp, 8 * k)
    assert key in t
    t = t.replace(key, key.replace('(S.mem.readLE (z.toNat', '(s.mem.readLE (z.toNat'), 1)
sys.stdout.write(t)
