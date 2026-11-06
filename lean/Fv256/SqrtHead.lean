import Fv256.Spec
import Fv256.Util
import Fv256.SqrtMath

/-! Arithmetic of the start of `Sqrt` (uint64 path): the shift count `cl = (bitlen + 1) / 2` and `rbx = 2^cl`. -/

namespace Fv256.SqrtHead

open Fv256

theorem bl_ge2 (x0 : Nat) (h2 : 2 ≤ x0) : 2 ≤ Spec.bitLen x0 := by
  have hb := Util.bitLen_bounds x0 (by omega)
  refine Classical.byContradiction fun hc => ?_
  have : Spec.bitLen x0 ≤ 1 := by omega
  have h3 : 2 ^ Spec.bitLen x0 ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) this
  omega

/-- the machine's `cl`: `((63 - clz) + 2) >> 1` -/
theorem cl_val (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) :
    ((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x0) + 2#64) >>> 1).toNat = (Spec.bitLen x0 + 1) / 2 := by
  have h1 := Util.clz_bl 64 x0 h64
  have h3 := bl_ge2 x0 h2
  have hn : Spec.bitLen x0 ≤ 64 := by
    have hb := Util.bitLen_bounds x0 (by omega)
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 64 ≤ 2 ^ (Spec.bitLen x0 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Nat.reduceMod]
  have : (63 - Janus.Arm64.clzNat 64 x0) = Spec.bitLen x0 - 1 := by omega
  rw [this]
  have e : (Spec.bitLen x0 - 1) % 18446744073709551616 = Spec.bitLen x0 - 1 := Nat.mod_eq_of_lt (by omega)
  rw [e]
  have e2 : (Spec.bitLen x0 - 1 + 2) % 18446744073709551616 = Spec.bitLen x0 + 1 := by
    rw [show Spec.bitLen x0 - 1 + 2 = Spec.bitLen x0 + 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
  have e3 : (2#64).toNat = 2 := rfl
  rw [e3, e2]

theorem cl_range (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) : 1 ≤ (Spec.bitLen x0 + 1) / 2 ∧ (Spec.bitLen x0 + 1) / 2 ≤ 32 := by
  have h3 := bl_ge2 x0 h2
  have hn : Spec.bitLen x0 ≤ 64 := by
    have hb := Util.bitLen_bounds x0 (by omega)
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 64 ≤ 2 ^ (Spec.bitLen x0 - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-- `rbx = 1 << cl` as a number -/
theorem shl_val (k : Nat) (hk : k ≤ 32) : (1#64 <<< k).toNat = 2 ^ k := by
  rw [BitVec.toNat_shiftLeft]
  show 1 <<< k % 2 ^ 64 = 2 ^ k
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) (by decide))

/-- the infeasible branch: for `x0 ≥ 2` the shift count is never `0 mod 64` -/
theorem cl_ne_zero (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) :
    ¬ (((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x0) + 2#64) >>> 1).toNat % 64 = 0) := by
  rw [cl_val x0 h2 h64]
  have := cl_range x0 h2 h64
  omega

/-- the start value satisfies the invariant -/
theorem init_inv (x0 : Nat) (h2 : 2 ≤ x0) (h64 : x0 < 2 ^ 64) :
    x0 < (2 ^ ((Spec.bitLen x0 + 1) / 2) + 1) * (2 ^ ((Spec.bitLen x0 + 1) / 2) + 1) :=
  SqrtMath.inv_init x0 (Spec.bitLen x0) (Util.bitLen_bounds x0 (by omega)).2

/-- the first-iteration facts of the 256-bit path, from the bit length `bl` of `X` (`65 ≤ bl ≤ 256`) and `cnt = (bl+1)/2` -/
theorem head_arith (X bl cnt : Nat) (hbl : Spec.bitLen X = bl) (h65 : 65 ≤ bl) (h256 : bl ≤ 256)
    (hcnt : cnt = (bl + 1) / 2) :
    1 ≤ cnt ∧ cnt ≤ 128 ∧ X < (2 ^ cnt + 1) * (2 ^ cnt + 1) ∧ 2 ^ 64 ≤ X ∧ X < 2 ^ 256 := by
  have hX0 : X ≠ 0 := by
    intro h; subst h
    simp [Spec.bitLen] at hbl; omega
  have hb := Util.bitLen_bounds X hX0
  rw [hbl] at hb
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · rw [hcnt]; exact SqrtMath.inv_init X bl hb.2
  · have : 2 ^ 64 ≤ 2 ^ (bl - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have : 2 ^ bl ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) h256
    omega

theorem shr1_add (a c : Nat) (h : a + c < 2 ^ 64) :
    ((BitVec.ofNat 64 a + BitVec.ofNat 64 c) >>> 1).toNat = (a + c) / 2 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.pow_one, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : c < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt h]

theorem bl_pos (v : Nat) (h : v ≠ 0) : 1 ≤ Spec.bitLen v := by
  have := Util.bitLen_bounds v h
  refine Classical.byContradiction fun hc => ?_
  have h0 : Spec.bitLen v = 0 := by omega
  rw [h0] at this
  simp at this
  omega

end Fv256.SqrtHead
