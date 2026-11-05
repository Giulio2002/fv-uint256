import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2

open Janus Janus.Arm64 Janus.Tactic

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

theorem wv4_chain7 (m : Memory) (sp x v1 v2 v3 : Nat) (h : x + 32 ≤ sp - 456 ∨ sp + 16 ≤ x) (hsp : 456 ≤ sp) :
    Fv256.B.wv (((((((m.writeLE (sp - 112) 8 v1).writeLE (sp - 120) 8 v2).writeLE (sp + 8) 8 v3).writeLE (sp - 40) 8 0).writeLE
      (sp - 32) 8 0).writeLE (sp - 24) 8 0).writeLE (sp - 16) 8 0) x 4 = Fv256.B.wv m x 4 := by
  rw [Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]

theorem copyout_frame (m m' : Memory) (z sp v1 v2 v3 a b c d : Nat) (hsp : 456 ≤ sp)
    (hz : z + 32 ≤ sp - 456 ∨ sp + 16 ≤ z)
    (hf : Janus.MemFrame (((((((m.writeLE (sp - 112) 8 v1).writeLE (sp - 120) 8 v2).writeLE (sp + 8) 8 v3).writeLE (sp - 40) 8 0).writeLE
      (sp - 32) 8 0).writeLE (sp - 24) 8 0).writeLE (sp - 16) 8 0) m'
      [(sp - 40, sp - 40 + 8 * 4), (sp - 112 - 344, sp - 112 - 8), (sp - 112 + 8, sp - 112 + 72)]) :
    Janus.MemFrame m ((((m'.writeLE z 8 a).writeLE (z + 8) 8 b).writeLE (z + 16) 8 c).writeLE (z + 24) 8 d)
      [(z, z + 32), (sp - 456, sp - 8), (sp + 8, sp + 16)] := by
  constructor
  · intro x n hx
    simp only [Outside, and_true] at hx
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [hf.readLE x n (by simp only [Outside, and_true]; omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · intro x n w
    simp only [Memory.accessible_writeLE]
    rw [hf.accessible]
    simp only [Memory.accessible_writeLE]

theorem val_close (S X Y : Nat) (hq : S = X / Y) (hy : Y ≠ 0) : S = Fv256.B.divSpec X Y := by
  rw [Fv256.B.divSpec, if_neg hy]; exact hq

theorem ysum_ne (y0 y1 y2 y3 : Nat)
    (h : ¬(((y1 = 0 ∧ y0 = 0) ∧ y2 = 0) ∧ y3 = 0)) :
    y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
      6277101735386680763835789423207666416102355444464034512896 * y3 ≠ 0 := by
  omega

theorem early_frame (m : Memory) (z sp v1 v2 a b c d : Nat) (hsp : 456 ≤ sp)
    (hz : z + 32 ≤ sp - 456 ∨ sp + 16 ≤ z) :
    Janus.MemFrame m ((((((m.writeLE (sp - 112) 8 v1).writeLE (sp - 120) 8 v2).writeLE (z + 16) 8 c).writeLE (z + 24) 8 d).writeLE z 8 a).writeLE (z + 8) 8 b)
      [(z, z + 32), (sp - 456, sp - 8), (sp + 8, sp + 16)] := by
  constructor
  · intro x n hx
    simp only [Outside, and_true] at hx
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · intro x n w
    simp only [Memory.accessible_writeLE]

theorem close_zero (X : Nat) : 0 = Fv256.B.divSpec X 0 := by
  simp [Fv256.B.divSpec]

theorem close_lt (X Y : Nat) (h : ¬ Y ≤ X) : 0 = Fv256.B.divSpec X Y := by
  rw [Fv256.B.divSpec]; split
  · rfl
  · exact (Nat.div_eq_of_lt (by omega)).symm

theorem close_eq (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) (hx0 : x0 < 18446744073709551616) (hx1 : x1 < 18446744073709551616) (hx2 : x2 < 18446744073709551616)
    (hx3 : x3 < 18446744073709551616) (hy0 : y0 < 18446744073709551616) (hy1 : y1 < 18446744073709551616) (hy2 : y2 < 18446744073709551616) (hy3 : y3 < 18446744073709551616)
    (hne : ¬(((y1 = 0 ∧ y0 = 0) ∧ y2 = 0) ∧ y3 = 0))
    (hxor : x3 ^^^ y3 = 0 ∧ (y0 ^^^ x0 = 0 ∧ y1 ^^^ x1 = 0) ∧ x2 ^^^ y2 = 0) :
    1 = Fv256.B.divSpec (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3)
      (y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
        6277101735386680763835789423207666416102355444464034512896 * y3) := by
  obtain ⟨a3, ⟨a0, a1⟩, a2⟩ := hxor
  have e3 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a3
  have e0 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a0
  have e1 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a1
  have e2 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a2
  subst e3 e0 e1 e2
  have := ysum_ne _ _ _ _ hne
  rw [Fv256.B.divSpec, if_neg this]
  exact (Nat.div_self (Nat.pos_of_ne_zero this)).symm

/-- the early-return writes of `Mod` (frame push at sp-144 and sp-152, then four stores into `z`, in any order) -/
theorem mod_early_frame (m : Memory) (z sp v1 v2 p1 p2 p3 p4 a b c d : Nat) (hsp : 488 ≤ sp)
    (hz : z + 32 ≤ sp - 488 ∨ sp + 16 ≤ z)
    (h1 : z ≤ p1 ∧ p1 + 8 ≤ z + 32) (h2 : z ≤ p2 ∧ p2 + 8 ≤ z + 32)
    (h3 : z ≤ p3 ∧ p3 + 8 ≤ z + 32) (h4 : z ≤ p4 ∧ p4 + 8 ≤ z + 32) :
    Janus.MemFrame m ((((((m.writeLE (sp - 144) 8 v1).writeLE (sp - 152) 8 v2).writeLE p1 8 a).writeLE p2 8 b).writeLE p3 8 c).writeLE p4 8 d)
      [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] := by
  have r1 : (sp - 488, sp - 8) ∈ [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] := by simp
  have r0 : (z, z + 32) ∈ [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] := by simp
  exact ((((((MemFrame.refl m _).writeLE v1 r1 (by simp; omega) (by simp; omega)).writeLE v2 r1 (by simp; omega) (by simp; omega)).writeLE a r0 h1.1 h1.2).writeLE b r0 h2.1 h2.2).writeLE c r0 h3.1 h3.2).writeLE d r0 h4.1 h4.2

/-- compose a pre-call frame with the callee's frame, then four stores into `z` -/
theorem mod_copy_frame (m M0 m' : Memory) (z sp p1 p2 p3 p4 a b c d : Nat) (rs : List (Nat × Nat)) (hsp : 488 ≤ sp)
    (hz : z + 32 ≤ sp - 488 ∨ sp + 16 ≤ z)
    (h1 : z ≤ p1 ∧ p1 + 8 ≤ z + 32) (h2 : z ≤ p2 ∧ p2 + 8 ≤ z + 32)
    (h3 : z ≤ p3 ∧ p3 + 8 ≤ z + 32) (h4 : z ≤ p4 ∧ p4 + 8 ≤ z + 32)
    (hM0 : Janus.MemFrame m M0 [(sp - 488, sp - 8), (sp + 8, sp + 16)])
    (hf : Janus.MemFrame M0 m' rs)
    (hrs : ∀ x n, Outside x n [(sp - 488, sp - 8), (sp + 8, sp + 16)] → Outside x n rs) :
    Janus.MemFrame m ((((m'.writeLE p1 8 a).writeLE p2 8 b).writeLE p3 8 c).writeLE p4 8 d)
      [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] := by
  have r0 : (z, z + 32) ∈ [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] := by simp
  have base : Janus.MemFrame m m' [(z, z + 32), (sp - 488, sp - 8), (sp + 8, sp + 16)] :=
    hM0.trans hf (fun x n hx => by
      simp only [Outside, and_true] at hx
      exact ⟨by simp only [Outside, and_true]; omega, hrs x n (by simp only [Outside, and_true]; omega)⟩)
  exact ((((base.writeLE a r0 h1.1 h1.2).writeLE b r0 h2.1 h2.2).writeLE c r0 h3.1 h3.2).writeLE d r0 h4.1 h4.2)

theorem mclose_zero (X : Nat) : 0 = Fv256.B.modSpec X 0 := by
  simp [Fv256.B.modSpec]

theorem mclose_lt (X Y : Nat) (h : ¬ Y ≤ X) (hy : Y ≠ 0) : X = Fv256.B.modSpec X Y := by
  rw [Fv256.B.modSpec, if_neg hy]; exact (Nat.mod_eq_of_lt (by omega)).symm

theorem mclose_eq (x0 x1 x2 x3 y0 y1 y2 y3 : Nat)
    (hne : ¬(((y1 = 0 ∧ y0 = 0) ∧ y2 = 0) ∧ y3 = 0))
    (hxor : x3 ^^^ y3 = 0 ∧ (y0 ^^^ x0 = 0 ∧ y1 ^^^ x1 = 0) ∧ x2 ^^^ y2 = 0) :
    0 = Fv256.B.modSpec (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3)
      (y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
        6277101735386680763835789423207666416102355444464034512896 * y3) := by
  obtain ⟨a3, ⟨a0, a1⟩, a2⟩ := hxor
  have e3 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a3
  have e0 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a0
  have e1 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a1
  have e2 := Fv256.B.xor_eq_zero_nat _ _ |>.mp a2
  subst e3 e0 e1 e2
  have := ysum_ne _ _ _ _ hne
  rw [Fv256.B.modSpec, if_neg this]
  exact (Nat.mod_self _).symm

theorem mval_close (S X Y : Nat) (hq : S = X % Y) (hy : Y ≠ 0) : S = Fv256.B.modSpec X Y := by
  rw [Fv256.B.modSpec, if_neg hy]; exact hq

end Fv256.Arm64.DivLemmas
