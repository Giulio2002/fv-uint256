#!/usr/bin/env python3 -I
# rsh_arm.py : writes lean/Fv256/Arm64/Rsh.lean (derived from lsh_arm.py output structure)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
M = '18446744073709551616'
def lim(v, i):
    return f"(Util.readLE8_lt s.mem ({v}.toNat + {8*i}))" if i else f"(Util.readLE8_lt s.mem {v}.toNat)"
def hand(v):
    b = [lim(v, i) for i in range(4)]
    pre = "generalize hm : n.toNat = m at *"
    def args(t): return f"_ _ _ _ {t} ht {b[0]} {b[1]} {b[2]} {b[3]}"
    h4 = [pre, "obtain rfl : m = 0 := (by omega)", "simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]"]
    h3 = [pre, "by_cases hlt : m - 192 < 64",
          "· obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩",
          "  have hq : 192 + t - 192 = t := (by omega)",
          "  simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]",
          "  simp only [Spec.rsh]",
          f"  rw [Nat.mod_eq_of_lt {b[3]}, Util.rsh3_t {args('t')}]",
          "· simp only [if_neg hlt]",
          "  simp only [Spec.rsh]",
          f"  rw [Util.rsh_big _ _ (by have := {b[0]}; have := {b[1]}; have := {b[2]}; have := {b[3]}; omega) (by omega)]",
          "  simp"]
    h2 = [pre, "obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩",
          f"have hc : {M} - (128 + t) - 18446744073709551424 = 64 - t := (by omega)",
          "have hp : (128 + t - 128) % 64 = t := (by omega)",
          "simp only [hc, hp]",
          f"rw [Util.shr_or_bv _ _ t ht {b[3]} {b[2]}]",
          f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
          "simp only [Spec.rsh]",
          f"exact Util.rsh2_t {args('t')}"]
    h1 = [pre, "obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩",
          f"have hc : {M} - (64 + t) - 18446744073709551488 = 64 - t := (by omega)",
          "have hp : (64 + t - 64) % 64 = t := (by omega)",
          "simp only [hc, hp]",
          f"rw [Util.shr_or_bv _ _ t ht {b[2]} {b[1]}, Util.shr_or_bv _ _ t ht {b[3]} {b[2]}]",
          f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
          "simp only [Spec.rsh]",
          f"exact Util.rsh1_t {args('t')}"]
    h0 = [pre, "have ht1 : 1 ≤ m := (by omega)", "have ht : m < 64 := (by omega)",
          f"have hc : ({M} - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)",
          "simp only [hc, Nat.mod_eq_of_lt ht]",
          f"rw [Util.shr_or_nat _ _ m ht1 ht {b[1]} {b[0]}, Util.shr_or_nat _ _ m ht1 ht {b[2]} {b[1]}, Util.shr_or_nat _ _ m ht1 ht {b[3]} {b[2]}]",
          f"rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) {b[3]})]",
          "simp only [Spec.rsh]",
          f"exact Util.rsh0_t _ _ _ _ m ht {b[0]} {b[1]} {b[2]} {b[3]}"]
    return h4, h3, h2, h0, h1
def block(v):
    h4, h3, h2, h0, h1 = hand(v)
    lim_ = "".join(f"have := Util.readLE8_lt s.mem ({p}.toNat{'' if o == 0 else ' + ' + str(o)}); " for p in (('z', 'x') if v == 'x' else ('z',)) for o in (0, 8, 16, 24))
    out = "    simp only [Disjoint] at *\n    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]\n"
    for h in (h4, h3, h2, h0, h1):
        out += "    · " + lim_ + h[0] + "\n" + "".join("      " + l + "\n" for l in h[1:])
    return out
t = open(ROOT+'/lean/Fv256/Arm64/Lsh.lean').read()
k = t.index("  rcases hzx with rfl | hzx")
k2 = t.index("\nnamespace Witness")
t = t[:k] + "  rcases hzx with rfl | hzx\n  · " + block('z').lstrip() + "  · " + block('x').lstrip() + t[k2:]
t = t.replace('Lsh', 'Rsh').replace('Spec.lsh', 'Spec.rsh').replace('x << n', 'x >> n').replace('Fv256.Spec.rsh` of the number at `x`, shifted by `n`,', 'Fv256.Spec.rsh` of the number at `x`, shifted right by `n`,').replace('holding the shifted value of `x`', 'holding the shifted value of `x`')
open(ROOT+'/lean/Fv256/Arm64/Rsh.lean', 'w').write(t)
