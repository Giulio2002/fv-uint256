import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF

open Janus Janus.Arm64 Janus.Tactic

namespace Fv256.Arm64.MdorLemmas

/-- Eight consecutive zero word stores zero the eight words. -/
theorem wv_zero8w (m : Memory) (a b c d e f g h : Nat) (hb : b = a + 8) (hc : c = a + 16) (hd : d = a + 24)
    (he : e = a + 32) (hf : f = a + 40) (hg : g = a + 48) (hh : h = a + 56) :
    Fv256.B.wv ((((((((m.writeLE a 8 0).writeLE b 8 0).writeLE c 8 0).writeLE d 8 0).writeLE e 8 0).writeLE f 8 0).writeLE g 8 0).writeLE h 8 0) a 8 = 0 := by
  subst hb hc hd he hf hg hh
  simp only [Fv256.B.wv]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

/-- the overflow flag: the `cset ne` form against the `MulDivOverflow` extraction form -/
theorem flag_conv (r80 r88 r96 r104 : Nat) (b : Bool)
    (h : (if (((r96 = 0 ∧ r104 = 0) ∧ r88 = 0) ∧ r80 = 0) then (0 : BitVec 8) else 1).toNat = b.toNat) :
    (if (r80 = 0 ∧ r88 = 0 ∧ r96 = 0 ∧ r104 = 0) then (0 : BitVec 64) else 1).toNat = if b = true then 1 else 0 := by
  by_cases hc : r80 = 0 ∧ r88 = 0 ∧ r96 = 0 ∧ r104 = 0
  · have hc' : ((r96 = 0 ∧ r104 = 0) ∧ r88 = 0) ∧ r80 = 0 := ⟨⟨⟨hc.2.2.1, hc.2.2.2⟩, hc.2.1⟩, hc.1⟩
    rw [if_pos hc'] at h
    rw [if_pos hc]
    cases b <;> simp_all
  · have hc' : ¬ (((r96 = 0 ∧ r104 = 0) ∧ r88 = 0) ∧ r80 = 0) := fun h' => hc ⟨h'.2, h'.1.2, h'.1.1.1, h'.1.1.2⟩
    rw [if_neg hc'] at h
    rw [if_neg hc]
    cases b <;> simp_all

theorem tail_flag (M1 M : Memory) (sp X Y D : Nat) (hsp : 136 ≤ sp) (hD : D ≠ 0) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (hmulv : Fv256.B.wv M1 (sp - 72) 8 = X * Y) (hq : Fv256.B.wv M (sp - 136) 8 = Fv256.B.wv M1 (sp - 72) 8 / D) :
    (if (M.readLE (sp - 80) 8 = 0 ∧ M.readLE (sp - 88) 8 = 0 ∧ M.readLE (sp - 96) 8 = 0 ∧ M.readLE (sp - 104) 8 = 0)
      then (0 : BitVec 64) else 1).toNat = if Fv256.F.muldivOv X Y D = true then 1 else 0 :=
  flag_conv _ _ _ _ _ (Fv256.F.mdo_main X Y D sp M hsp hD hX hY (by rw [hq, hmulv])).1

theorem tail_z (M1 M : Memory) (sp X Y D : Nat) (hsp : 136 ≤ sp) (hD : D ≠ 0) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (hmulv : Fv256.B.wv M1 (sp - 72) 8 = X * Y) (hq : Fv256.B.wv M (sp - 136) 8 = Fv256.B.wv M1 (sp - 72) 8 / D) :
    M.readLE (sp - 136) 8 + 18446744073709551616 * M.readLE (sp - 128) 8 +
        340282366920938463463374607431768211456 * M.readLE (sp - 120) 8 +
      6277101735386680763835789423207666416102355444464034512896 * M.readLE (sp - 112) 8 = Fv256.F.muldivSpec X Y D := by
  have h := (Fv256.F.mdo_main X Y D sp M hsp hD hX hY (by rw [hq, hmulv])).2
  simpa only [Nat.reducePow] using h

theorem tail_m (M1 : Memory) (sp X Y D v : Nat) (hD : D ≠ 0) (hmulv : Fv256.B.wv M1 (sp - 72) 8 = X * Y)
    (hrm : v = Fv256.B.wv M1 (sp - 72) 8 % D) : v = Fv256.F.mulmodSpec X Y D := by
  rw [hrm, hmulv]
  simp only [Fv256.F.mulmodSpec]
  split
  · rename_i h; exact absurd h hD
  · rfl

end Fv256.Arm64.MdorLemmas
