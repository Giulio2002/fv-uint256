import Janus
import Fv256.SpecI

/-!
# Utilities for family I (decimal parsers): `runtime.cmpstring` against the lexicographic order of `SpecI`
-/

namespace Fv256.I

open Janus Janus.Contracts.Cmpstring

/-- `cmpstring(a, b) = 1` on strings of the same length `n` is exactly `lexGt`. -/
theorem strCmp_eq_one_iff (m : Janus.Arm64.Memory) : ∀ (n a b : Nat),
    strCmp m a b n n = 1 ↔ lexGt (fun k => m.readLE (a + k) 1) (fun k => m.readLE (b + k) 1) n
  | 0, a, b => by simp [strCmp, lexGt]
  | n + 1, a, b => by
    simp only [strCmp]
    by_cases h1 : m.readLE a 1 < m.readLE b 1
    · rw [if_pos h1]
      simp only [Int.reduceNeg, reduceCtorEq, false_iff]
      rintro ⟨k, hk, hpre, hlt⟩
      rcases Nat.eq_zero_or_pos k with rfl | hkp
      · simp only [Nat.add_zero] at hlt; omega
      · have := hpre 0 hkp; simp only [Nat.add_zero] at this; omega
    · rw [if_neg h1]
      by_cases h2 : m.readLE b 1 < m.readLE a 1
      · rw [if_pos h2]
        simp only [true_iff]
        exact ⟨0, by omega, fun j hj => by omega, by simpa using h2⟩
      · rw [if_neg h2]
        have heq : m.readLE a 1 = m.readLE b 1 := by omega
        rw [strCmp_eq_one_iff m n (a + 1) (b + 1)]
        constructor
        · rintro ⟨k, hk, hpre, hlt⟩
          refine ⟨k + 1, by omega, fun j hj => ?_, ?_⟩
          · rcases Nat.eq_zero_or_pos j with rfl | hjp
            · simpa using heq
            · have := hpre (j - 1) (by omega)
              simpa [show a + 1 + (j - 1) = a + j by omega, show b + 1 + (j - 1) = b + j by omega] using this
          · simpa [show a + 1 + k = a + (k + 1) by omega, show b + 1 + k = b + (k + 1) by omega] using hlt
        · rintro ⟨k, hk, hpre, hlt⟩
          rcases Nat.eq_zero_or_pos k with rfl | hkp
          · simp only [Nat.add_zero] at hlt; omega
          · refine ⟨k - 1, by omega, fun j hj => ?_, ?_⟩
            · have := hpre (j + 1) (by omega)
              simpa [show a + 1 + j = a + (j + 1) by omega, show b + 1 + j = b + (j + 1) by omega] using this
            · simpa [show a + 1 + (k - 1) = a + k by omega, show b + 1 + (k - 1) = b + k by omega] using hlt


/-- `(0 - d) >>s 63` is all ones for `0 < d < 2^63` (Go's branch-free index mask `i & ((0 - (len - i)) >> 63)`). -/
theorem sshr63_neg (d : BitVec 64) (h0 : 0 < d.toNat) (h1 : d.toNat < 2 ^ 63) :
    (0#64 - d).sshiftRight 63 = BitVec.allOnes 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_allOnes, hj, decide_true]
  have hmsb : (0#64 - d).msb = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  by_cases h' : 63 + j < 64
  · simp [h']
    have : j = 0 := by omega
    subst this
    simpa [BitVec.msb_eq_getLsbD_last] using hmsb
  · simpa [h', hj] using hmsb

theorem mask_keep (d k : BitVec 64) (h0 : 0 < d.toNat) (h1 : d.toNat < 2 ^ 63) :
    ((0#64 - d).sshiftRight 63).toNat &&& k.toNat = k.toNat := by
  rw [sshr63_neg d h0 h1, BitVec.toNat_allOnes]
  have ha : k.toNat < 2 ^ 64 := k.isLt
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt ha]


theorem jle32_not_127 (E : BitVec 32)
    (h : ¬(E - 127#32 = 0#32 ∨ ((E - 127#32).msb != !decide ((E - 127#32).toInt = E.toInt - 127 - 0)) = true)) :
    128 ≤ E.toNat := by
  by_cases hc : E.toNat ≤ 127
  · exfalso; apply h
    have hv : (E - 127#32).toNat = 4294967169 + E.toNat - (if E.toNat = 127 then 4294967296 else 0) := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      split <;> omega
    have hEi : E.toInt = E.toNat := by rw [BitVec.toInt_eq_toNat_of_lt]; omega
    by_cases he : E.toNat = 127
    · left
      apply BitVec.eq_of_toNat_eq
      rw [hv]; simp [he]
    · right
      have hv' : (E - 127#32).toNat = 4294967169 + E.toNat := by rw [hv]; simp [he]
      have hmsb : (E - 127#32).msb = true := by
        rw [BitVec.msb_eq_decide]; simp [hv']; omega
      have hti : (E - 127#32).toInt = (E.toNat : Int) - 127 := by
        rw [BitVec.toInt_eq_toNat_cond, hv']
        have : ¬ (2 * (4294967169 + E.toNat) < 2 ^ 32) := by omega
        simp [this]; omega
      simp [hmsb, hti, hEi]
  · omega

theorem jle32_not_2047 (E : BitVec 32)
    (h : ¬(E - 2047#32 = 0#32 ∨ ((E - 2047#32).msb != !decide ((E - 2047#32).toInt = E.toInt - 2047 - 0)) = true)) :
    2048 ≤ E.toNat := by
  by_cases hc : E.toNat ≤ 2047
  · exfalso; apply h
    have hv : (E - 2047#32).toNat = 4294965249 + E.toNat - (if E.toNat = 2047 then 4294967296 else 0) := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      split <;> omega
    have hEi : E.toInt = E.toNat := by rw [BitVec.toInt_eq_toNat_of_lt]; omega
    by_cases he : E.toNat = 2047
    · left
      apply BitVec.eq_of_toNat_eq
      rw [hv]; simp [he]
    · right
      have hv' : (E - 2047#32).toNat = 4294965249 + E.toNat := by rw [hv]; simp [he]
      have hmsb : (E - 2047#32).msb = true := by
        rw [BitVec.msb_eq_decide]; simp [hv']; omega
      have hti : (E - 2047#32).toInt = (E.toNat : Int) - 2047 := by
        rw [BitVec.toInt_eq_toNat_cond, hv']
        have : ¬ (2 * (4294965249 + E.toNat) < 2 ^ 32) := by omega
        simp [this]; omega
      simp [hmsb, hti, hEi]
  · omega

theorem ja32 (E E2 : BitVec 32)
    (h : ¬(¬((18446744073709486080 + E.toNat) % 4294967296 < 1048575) ∧
      ¬(BitVec.setWidth 32 (BitVec.setWidth 64 E2 - 65536#64) - 1048575#32 = 0#32)))
    (hE : E2 = E) : 65536 ≤ E.toNat := by
  subst hE
  by_cases hc : E2.toNat < 65536
  · exfalso; apply h
    have hE := E2.isLt
    refine ⟨by omega, ?_⟩
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    omega
  · omega

theorem g1 (E : BitVec 32) (hge : 128 ≤ (BitVec.setWidth 32 (BitVec.setWidth 64 E)).toNat) :
    128 ≤ (BitVec.setWidth 64 E).toNat := by
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le (by omega)] at hge
  have := E.isLt
  omega

theorem g1' (E : BitVec 32) (hge : 128 ≤ E.toNat) :
    128 ≤ (BitVec.setWidth 64 E).toNat := by
  rw [BitVec.toNat_setWidth_of_le (by omega)]; omega

theorem g2 (E : BitVec 32) : (BitVec.setWidth 64 E).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_setWidth_of_le (by omega)]; exact E.isLt

end Fv256.I
