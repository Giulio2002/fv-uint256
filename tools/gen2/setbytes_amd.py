#!/usr/bin/env python3 -I
# setbytes_amd.py N [probe|full] [below above]
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
n = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'probe'
below = int(sys.argv[3]) if len(sys.argv) > 3 else 8
above = int(sys.argv[4]) if len(sys.argv) > 4 else 24
s = open(ROOT+'/lean/Fv256/Proofs/Amd64/SetBytes32.lean').read()
s = s.replace('SetBytes32', f'SetBytes{n}').replace('32 ≤ len.toNat', f'{n} ≤ len.toNat').replace('len.toNat < 32', f'len.toNat < {n}')
s = s.replace('Buffer s ptr 32 false', f'Buffer s ptr {n} false').replace('Buffer s0 ptr 32 false', f'Buffer s0 ptr {n} false')
s = s.replace('(z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 32 ≤ z.toNat)', f'(z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + {n} ≤ z.toNat)')
s = s.replace('(ptr.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨', f'(ptr.toNat + {n} ≤ (s.regs regSP).toNat - 8 ∨').replace('(ptr.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨', f'(ptr.toNat + {n} ≤ (s0.regs regSP).toNat - 8 ∨')
s = s.replace('(fun i => s.mem.readLE (ptr.toNat + i) 1) 32', f'(fun i => s.mem.readLE (ptr.toNat + i) 1) {n}').replace('(fun i => s0.mem.readLE (ptr.toNat + i) 1) 32', f'(fun i => s0.mem.readLE (ptr.toNat + i) 1) {n}')
s = s.replace('[z, ptr, len, cap]', '[z, ptr, len, cap]')
s = s.replace('[z, ptr, 32, 32]', f'[z, ptr, {n}, {n}]').replace('z ptr 32 32 ret', f'z ptr {n} {n} ret').replace('z, ptr, 32, 32, hret', f'z, ptr, {n}, {n}, hret')
s = s.replace('if i = 1 then 32 else if i = 7 then 32', f'if i = 1 then {n} else if i = 7 then {n}')
s = s.replace('32 ≤ (32 : BitVec 64).toNat', f'{n} ≤ ({n} : BitVec 64).toNat')
s = s.replace('first 32 bytes', f'first {n} bytes').replace('the 32 bytes at `ptr`', f'the {n} bytes at `ptr`').replace('`len ≥ 32`', f'`len ≥ {n}`').replace('`len < 32`', f'`len < {n}`')
s = s.replace('StackWritable s 8 24', f'StackWritable s {below} {above}').replace('StackWritable s0 8 24', f'StackWritable s0 {below} {above}')
s = s.replace('(s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24', f'(s.regs regSP).toNat - {below} ∨ (s.regs regSP).toNat + {above}')
s = s.replace('(s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24', f'(s0.regs regSP).toNat - {below} ∨ (s0.regs regSP).toNat + {above}')
s = s.replace('((s.regs regSP).toNat - 8) 32)', f'((s.regs regSP).toNat - {below}) {below+above})').replace('((s0.regs regSP).toNat - 8) 32', f'((s0.regs regSP).toNat - {below}) {below+above}')
s = s.replace('window `[RSP-8, RSP+24)`', f'window `[RSP-{below}, RSP+{above})`')
if n != 32:
    s = s.replace("(hpre : StackWritable s 16 24) :", "(hpre : StackWritable s 16 24) (hzb : Buffer s z 32 true) :")
    s = s.replace("  obtain ⟨hle, hnw, hacc⟩ := hpre\n", "  obtain ⟨hle, hnw, hacc⟩ := hpre\n  obtain ⟨hzw, hz⟩ := hzb\n")
if mode == 'full':
    hv = ''.join(f"have := Util.rd1_lt s.mem (ptr.toNat{'' if i==0 else ' + '+str(i)}); " for i in range(n))
    BV = "BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Util.revBytes_readLE"
    Z = "Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero"
    BV = BV.replace(", Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero", "")
    h2 = ''.join(f"have := Util.rd2_lt s.mem (ptr.toNat{'' if i==0 else ' + '+str(i)}); " for i in range(max(n-1,1)))
    def _a(i): return "ptr.toNat" + ('' if i == 0 else ' + ' + str(i))
    h2 += ''.join(f"have h2b{i} : s.mem.readLE ({_a(i)}) 2 = s.mem.readLE ({_a(i)}) 1 + 256 * s.mem.readLE ({_a(i+1)}) 1 := Util.rd2_bytes s.mem ({_a(i)}); " for i in range(max(n-1,1)))
    T = ("  · " + hv + h2 + f"(try simp only [{Z}]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [{BV}]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; "
         "(try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))\n")
    i = s.index("  refine ⟨?_, ?_⟩\n  · rw [Util.be32_rev]")
    j = s.index("  · simp (disch := omega) only [Util.ow2_wl_iff")
    s = s[:i] + "  refine ⟨?_, ?_⟩\n" + T + s[j:]
if mode == 'probe':
    i = s.index("  refine ⟨?_, ?_⟩")
    j = s.index("\n/-- Out of bounds")
    s = s[:i] + "  trace_state\n  all_goals sorry\n" + s[j:]
s = s.replace('theorem correctness','set_option maxHeartbeats 8000000 in\ntheorem correctness',1) if 'maxHeartbeats' not in s else s
s = s.replace('theorem correctness','set_option maxHeartbeats 8000000 in\ntheorem correctness',1) if 'maxHeartbeats' not in s else s
open((ROOT+f'/lean/Fv256/Proofs/Amd64/SetBytes{n}.lean'), 'w').write(s)
