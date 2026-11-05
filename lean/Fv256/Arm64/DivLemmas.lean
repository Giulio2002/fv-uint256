import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2

open Janus.Arm64

namespace Fv256.Arm64.DivLemmas

/-- Four consecutive zero word stores zero the four words. -/
theorem wv_zero4w (m : Memory) (a b c d : Nat) (hb : b = a + 8) (hc : c = a + 16) (hd : d = a + 24) :
    Fv256.B.wv ((((m.writeLE a 8 0).writeLE b 8 0).writeLE c 8 0).writeLE d 8 0) a 4 = 0 := by
  subst hb hc hd
  simp only [Fv256.B.wv]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

theorem dec_div (X : Nat) (h : X < 2 * 18446744073709551616) :
    (decide (18446744073709551616 ≤ X)).toNat = X / 18446744073709551616 := by
  by_cases hh : 18446744073709551616 ≤ X
  · simp only [hh, decide_true, Bool.toNat_true]; omega
  · simp only [hh, decide_false, Bool.toNat_false]; omega

theorem wc_c (a b : Nat) (c : Bool) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    (addWithCarry (BitVec.ofNat 64 a) (~~~BitVec.ofNat 64 b) c).snd.c =
      decide (18446744073709551616 ≤ a + (18446744073709551616 - 1 - b) + c.toNat) := by
  simp only [addWithCarry, BitVec.toNat_ofNat, BitVec.toNat_not]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have := Bool.toNat_le c
  simp only [Nat.reducePow]
  apply decide_eq_decide.mpr
  omega

theorem chain_zero_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (18446744073709551616 -
        (addWithCarry (0#64) (18446744073709551615#64)
          (addWithCarry (BitVec.ofNat 64 a3) (~~~BitVec.ofNat 64 b3)
            (addWithCarry (BitVec.ofNat 64 a2) (~~~BitVec.ofNat 64 b2)
              (addWithCarry (BitVec.ofNat 64 a1) (~~~BitVec.ofNat 64 b1)
                (decide (b0 ≤ a0))).snd.c).snd.c).snd.c).fst.toNat) % 18446744073709551616 = 0 ↔
    b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 := by
  have key := Util.borrow4_dec' a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  rw [wc_c _ _ _ h1 g1, wc_c _ _ _ h2 g2, wc_c _ _ _ h3 g3]
  have t0 := Bool.toNat_le (decide (b0 ≤ a0))
  rw [dec_div (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) (by omega)]
  rw [dec_div (a2 + (18446744073709551616 - 1 - b2) + (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) (by omega)]
  simp only [addWithCarry, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_add]
  rw [dec_div (a3 + (18446744073709551616 - 1 - b3) + (a2 + (18446744073709551616 - 1 - b2) + (a1 + (18446744073709551616 - 1 - b1) + (decide (b0 ≤ a0)).toNat) / 18446744073709551616) / 18446744073709551616) (by omega)]
  by_cases hc : b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3
  · simp only [hc, iff_true]; rw [if_pos hc] at key; omega
  · simp only [hc, iff_false]; rw [if_neg hc] at key; omega

end Fv256.Arm64.DivLemmas
