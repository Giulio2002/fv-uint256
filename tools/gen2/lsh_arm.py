#!/usr/bin/env python3 -I
# lsh_arm.py [debug]  : writes lean/Fv256/Arm64/Lsh.lean
import sys
debug = len(sys.argv) > 1
M = '18446744073709551616'
def lim(v, i):
    return f"(Util.readLE8_lt s.mem ({v}.toNat + {8*i}))" if i else f"(Util.readLE8_lt s.mem {v}.toNat)"
def hand(v):
    b = [lim(v, i) for i in range(4)]
    pre = "generalize hm : n.toNat = m at *; "
    h0 = (pre + "have ht1 : 1 ≤ m := (by omega); have ht : m < 64 := (by omega); "
          f"have hc : ({M} - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega); "
          "simp only [hc, Nat.mod_eq_of_lt ht]; "
          f"rw [Util.shl_or_bv0 _ _ m ht1 ht {b[1]} {b[0]}, Util.shl_or_bv0 _ _ m ht1 ht {b[2]} {b[1]}, Util.shl_or_bv0 _ _ m ht1 ht {b[3]} {b[2]}]; "
          f"simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh0_t _ _ _ _ m ht {b[0]} {b[1]} {b[2]} {b[3]}")
    h1 = (pre + "obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, by omega, by omega⟩; "
          f"have hc : {M} - (64 + t) - 18446744073709551488 = 64 - t := (by omega); "
          "have hp : (64 + t - 64) % 64 = t := (by omega); simp only [hc, hp]; "
          f"rw [Util.shl_or_bv _ _ t ht {b[2]} {b[1]}, Util.shl_or_bv _ _ t ht {b[1]} {b[0]}]; "
          f"simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh1_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}")
    h2 = (pre + "obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, by omega, by omega⟩; "
          f"have hc : {M} - (128 + t) - 18446744073709551424 = 64 - t := (by omega); "
          "have hp : (128 + t - 128) % 64 = t := (by omega); simp only [hc, hp]; "
          f"rw [Util.shl_or_bv _ _ t ht {b[1]} {b[0]}]; "
          f"simp only [Spec.lsh, Spec.W, Nat.reducePow]; exact Util.lsh2_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}")
    h3 = [pre + "by_cases hlt : m - 192 < 64",
          "· obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩",
          "  have hq : 192 + t - 192 = t := (by omega)",
          "  simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ofNat, Nat.reducePow]",
          "  simp only [Spec.lsh, Spec.W, Nat.reducePow]",
          f"  exact Util.lsh3_t _ _ _ _ t ht {b[0]} {b[1]} {b[2]} {b[3]}",
          "· simp only [if_neg hlt]",
          "  simp only [Spec.lsh, Spec.W, Nat.reducePow]",
          "  rw [Util.lsh_big _ _ (by omega)]",
          "  simp"]
    h4 = (pre + "obtain rfl : m = 0 := (by omega); simp only [Spec.lsh, Spec.W, Nat.reducePow, Nat.pow_zero, Nat.mul_one]; "
          f"first | done | rw [Nat.mod_eq_of_lt (by have := {b[0]}; have := {b[1]}; have := {b[2]}; have := {b[3]}; omega)]")
    return [h4, h3, h2, h1, h0]
def block(v):
    h4, h3, h2, h0, h1 = hand(v)[0], hand(v)[1], hand(v)[2], hand(v)[4], hand(v)[3]
    lim = "".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o == 0 else ' + ' + str(o)}); " for p in ('z', 'x') for o in (0, 8, 16, 24)) if v == 'x' else "".join(f"have := Util.readLE8_lt s.mem (z.toNat{'' if o == 0 else ' + ' + str(o)}); " for o in (0, 8, 16, 24))
    out = "    simp only [Disjoint] at *\n    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]\n"
    for h in (h4, h3, h2, h0, h1):
        if isinstance(h, list):
            out += "    · " + lim + h[0] + "\n" + "".join("      " + l + "\n" for l in h[1:])
        else:
            out += "    · " + lim + h + "\n"
    return out
t = open('/srv/fv-uint256/lean/Fv256/Arm64/Neg.lean').read()
t = t.replace('Neg', 'Lsh').replace('(z x : BitVec 64)', '(z x n : BitVec 64)').replace('[z, x]', '[z, x, n]')
t = t.replace('Spec.neg (val256 s.mem x.toNat)', 'Spec.lsh (val256 s.mem x.toNat) n.toNat')
L = t.split('\n')
k = [i for i, l in enumerate(L) if l.startswith('  rcases hzx')][0]
k2 = [i for i, l in enumerate(L) if l.startswith('  all_goals first')][0]
L = L[:k] + ["  rcases hzx with rfl | hzx", "  · " + block('z').lstrip().replace("simp only [Disjoint] at *", "simp only [Disjoint] at *", 1)] + ["  · " + block('x').lstrip()] + L[k2+1:]
out = '\n'.join(L)
out = out.replace('(*uint256.Int).Lsh(x *Int) *Int` (arm64): `z = Fv256.Spec.neg x`', '(*uint256.Int).Lsh(x *Int, n uint) *Int` (arm64): `z = x << n`').replace('`z`, `x` are equal or disjoint', '`z`, `x` are equal or disjoint, and for any shift count `n` (`X2`, any 64-bit value; counts of 256 or more give zero)').replace('is `Fv256.Spec.neg` of the number at `x`', 'is `Fv256.Spec.lsh` of the number at `x`, shifted by `n`,').replace('holding `0`', 'holding the shifted value of `x`')
out = out.replace("if i = 0 then z else if i = 1 then x\n", "if i = 0 then z else if i = 1 then x else if i = 2 then n\n")
out = out.replace("def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)", "def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)\ndef n : BitVec 64 := 0#64")
out = out.replace("[z, x, n] s0 :=", "[z, x, n] s0 :=").replace("rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl", "rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl")
out = out.replace("∃ (ret : Nat) (s : State) (z x n : BitVec 64)", "∃ (ret : Nat) (s : State) (z x n : BitVec 64)").replace("⟨ret, s0, z, x, hret, setup, hpre⟩", "⟨ret, s0, z, x, n, hret, setup, hpre⟩")
out = out.replace("correctness z x ret hret s0 setup hpre", "correctness z x n ret hret s0 setup hpre")
open('/srv/fv-uint256/lean/Fv256/Arm64/Lsh.lean', 'w').write(out)
