import Fv256.UtilF

/-! Result extraction of `MulDivOverflow` for a quotient buffer of eight words at an arbitrary base `b`
(arm64 layout; `UtilF.mdo_main` has the amd64 base `sp - 136` fixed). -/

namespace Fv256.F
open Fv256.B

theorem mdo_main_at (X Y D b : Nat) (M : Janus.Arm64.Memory) (hD : D ≠ 0)
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hq : wv M b 8 = X * Y / D) :
    (if (((M.readLE (b + 40) 8 = 0 ∧ M.readLE (b + 32) 8 = 0) ∧ M.readLE (b + 48) 8 = 0) ∧ M.readLE (b + 56) 8 = 0)
      then 0#8 else 1#8).toNat = (muldivOv X Y D).toNat ∧
    M.readLE b 8 + 2 ^ 64 * M.readLE (b + 8) 8 + 2 ^ 128 * M.readLE (b + 16) 8 +
      2 ^ 192 * M.readLE (b + 24) 8 = muldivSpec X Y D := by
  have h := mdo_main X Y D (b + 136) M (by omega) hD hX hY (by rw [show b + 136 - 136 = b by omega]; exact hq)
  have e0 : b + 136 - 136 = b := by omega
  have e1 : b + 136 - 128 = b + 8 := by omega
  have e2 : b + 136 - 120 = b + 16 := by omega
  have e3 : b + 136 - 112 = b + 24 := by omega
  have e4 : b + 136 - 104 = b + 32 := by omega
  have e5 : b + 136 - 96 = b + 40 := by omega
  have e6 : b + 136 - 88 = b + 48 := by omega
  have e7 : b + 136 - 80 = b + 56 := by omega
  simp only [e0, e1, e2, e3, e4, e5, e6, e7] at h
  exact h

/-- eight consecutive 8-byte zero stores clear eight words -/
theorem wv_zero8 (m : Janus.Arm64.Memory) (p q1 q2 q3 q4 q5 q6 q7 : Nat) (h1 : q1 = p + 8) (h2 : q2 = p + 16)
    (h3 : q3 = p + 24) (h4 : q4 = p + 32) (h5 : q5 = p + 40) (h6 : q6 = p + 48) (h7 : q7 = p + 56) :
    wv (((((((m.writeLE p 8 0).writeLE q1 8 0).writeLE q2 8 0).writeLE q3 8 0).writeLE q4 8 0).writeLE q5 8 0).writeLE q6 8 0
      |>.writeLE q7 8 0) p 8 = 0 := by
  subst h1 h2 h3 h4 h5 h6 h7
  simp (disch := omega) only [wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]

/-- four consecutive 8-byte zero stores clear four words -/
theorem wv_zero4w (m : Janus.Arm64.Memory) (p q1 q2 q3 : Nat) (h1 : q1 = p + 8) (h2 : q2 = p + 16) (h3 : q3 = p + 24) :
    wv ((((m.writeLE p 8 0).writeLE q1 8 0).writeLE q2 8 0).writeLE q3 8 0) p 4 = 0 := by
  subst h1 h2 h3
  simp (disch := omega) only [wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]

/-- five consecutive 8-byte zero stores clear five words -/
theorem wv_zero5w (m : Janus.Arm64.Memory) (p q1 q2 q3 q4 : Nat) (h1 : q1 = p + 8) (h2 : q2 = p + 16) (h3 : q3 = p + 24)
    (h4 : q4 = p + 32) :
    wv (((((m.writeLE p 8 0).writeLE q1 8 0).writeLE q2 8 0).writeLE q3 8 0).writeLE q4 8 0) p 5 = 0 := by
  subst h1 h2 h3 h4
  simp (disch := omega) only [wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]

/-- the sum of four limbs is zero iff each limb is -/
theorem sum4_eq_zero (a b c d : Nat) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
      6277101735386680763835789423207666416102355444464034512896 * d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h; omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- adapting the amd64-shaped flag (`mdo_main`) to a 64-bit `cset` result with a differently nested condition -/
theorem flag64 (c1 c2 : Prop) [Decidable c1] [Decidable c2] (h : c1 ↔ c2) (ov : Bool)
    (H : (if c1 then 0#8 else 1#8).toNat = ov.toNat) :
    (if c2 then 0#64 else 1#64).toNat = (if ov = true then 1 else 0) := by
  by_cases hc : c1
  · have hc2 : c2 := h.mp hc
    rw [if_pos hc] at H
    rw [if_pos hc2]
    cases ov <;> simp_all
  · have hc2 : ¬ c2 := fun h2 => hc (h.mpr h2)
    rw [if_neg hc] at H
    rw [if_neg hc2]
    cases ov <;> simp_all

end Fv256.F
