import Fv256.UtilB
import Fv256.UdivremMath
import Fv256.SpecF

namespace Fv256.F
open Fv256.B

/-- more words never decrease the number -/
theorem wv_mono (M : Janus.Arm64.Memory) (p : Nat) : ∀ m n, m ≤ n → wv M p m ≤ wv M p n := by
  intro m n h
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · rw [e]; exact Nat.le_refl _
    · have := ih (by omega)
      rw [wv_snoc]; omega

/-- if `L` words hold the same number as the first `u ≤ k ≤ L` words, then so do `k` words -/
theorem wv_trunc (M : Janus.Arm64.Memory) (p u k L : Nat) (hu : u ≤ k) (hk : k ≤ L)
    (h : wv M p L = wv M p u) : wv M p k = wv M p u := by
  have h1 := wv_mono M p u k hu
  have h2 := wv_mono M p k L hk
  omega


/-- four 16-byte zero stores clear eight words -/
theorem wv_zero4 (m : Janus.Arm64.Memory) (p q r s : Nat) (h1 : q = p + 16) (h2 : r = p + 32) (h3 : s = p + 48) :
    wv ((((m.writeLE p 16 0).writeLE q 16 0).writeLE r 16 0).writeLE s 16 0) p 8 = 0 := by
  subst h1 h2 h3
  have e : ∀ a, p ≤ a → a + 8 ≤ p + 64 → (a - p) % 8 = 0 → ((((m.writeLE p 16 0).writeLE (p + 16) 16 0).writeLE (p + 32) 16 0).writeLE (p + 48) 16 0).readLE a 8 = 0 := by
    intro a h1 h2 h8
    rcases (by omega : a + 8 ≤ p + 16 ∨ (p + 16 ≤ a ∧ a + 8 ≤ p + 32) ∨ (p + 32 ≤ a ∧ a + 8 ≤ p + 48) ∨ (p + 48 ≤ a ∧ a + 8 ≤ p + 64)) with h | h | h | h
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_inside _ _ h1 h]
      simp
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_inside _ _ h.1 h.2]
      simp
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_inside _ _ h.1 h.2]
      simp
    · rw [Janus.Arm64.Memory.readLE_writeLE_inside _ _ h.1 h.2]
      simp
  simp only [wv, e p (by omega) (by omega) (by omega), e (p + 8) (by omega) (by omega) (by omega), e (p + 8 + 8) (by omega) (by omega) (by omega),
    e (p + 8 + 8 + 8) (by omega) (by omega) (by omega), e (p + 8 + 8 + 8 + 8) (by omega) (by omega) (by omega), e (p + 8 + 8 + 8 + 8 + 8) (by omega) (by omega) (by omega),
    e (p + 8 + 8 + 8 + 8 + 8 + 8) (by omega) (by omega) (by omega), e (p + 8 + 8 + 8 + 8 + 8 + 8 + 8) (by omega) (by omega) (by omega)]

theorem wv_zero4' (m : Janus.Arm64.Memory) (p q r s : Nat) (h1 : q = p + 16) (h2 : r = p + 32) (h3 : s = p + 48) :
    wv ((((m.writeLE p 16 (BitVec.toNat (0 : BitVec 128))).writeLE q 16 (BitVec.toNat (0 : BitVec 128))).writeLE r 16
      (BitVec.toNat (0 : BitVec 128))).writeLE s 16 (BitVec.toNat (0 : BitVec 128))) p 8 = 0 := by
  have e : BitVec.toNat (0 : BitVec 128) = 0 := rfl
  rw [e]
  exact wv_zero4 m p q r s h1 h2 h3


set_option exponentiation.threshold 600 in
theorem mul8_limbs (a0 a1 a2 a3 a4 a5 a6 a7 P : Nat) (hP : P < 2 ^ 512)
    (h0 : a0 = P % 2 ^ 64) (h1 : a1 = P / 2 ^ 64 % 2 ^ 64) (h2 : a2 = P / 2 ^ 128 % 2 ^ 64)
    (h3 : a3 = P / 2 ^ 192 % 2 ^ 64) (h4 : a4 = P / 2 ^ 256 % 2 ^ 64) (h5 : a5 = P / 2 ^ 320 % 2 ^ 64)
    (h6 : a6 = P / 2 ^ 384 % 2 ^ 64) (h7 : a7 = P / 2 ^ 448 % 2 ^ 64) :
    a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * (a3 + 2 ^ 64 * (a4 + 2 ^ 64 * (a5 + 2 ^ 64 * (a6 + 2 ^ 64 * (a7 + 2 ^ 64 * 0))))))) = P := by
  subst h0 h1 h2 h3 h4 h5 h6 h7
  simp only [Nat.reducePow] at *
  omega


set_option exponentiation.threshold 600 in
theorem mul8_limbs' (a0 a1 a2 a3 a4 a5 a6 a7 P : Nat) (hP : P < 2 ^ 512)
    (h0 : a0 % 2 ^ 64 = P % 2 ^ 64) (h1 : a1 % 2 ^ 64 = P / 2 ^ 64 % 2 ^ 64) (h2 : a2 % 2 ^ 64 = P / 2 ^ 128 % 2 ^ 64)
    (h3 : a3 % 2 ^ 64 = P / 2 ^ 192 % 2 ^ 64) (h4 : a4 % 2 ^ 64 = P / 2 ^ 256 % 2 ^ 64) (h5 : a5 % 2 ^ 64 = P / 2 ^ 320 % 2 ^ 64)
    (h6 : a6 % 2 ^ 64 = P / 2 ^ 384 % 2 ^ 64) (h7 : a7 % 2 ^ 64 = P / 2 ^ 448 % 2 ^ 64) :
    a0 % 256 ^ 8 + 2 ^ 64 * (a1 % 256 ^ 8 + 2 ^ 64 * (a2 % 256 ^ 8 + 2 ^ 64 * (a3 % 256 ^ 8 + 2 ^ 64 * (a4 % 256 ^ 8 +
      2 ^ 64 * (a5 % 256 ^ 8 + 2 ^ 64 * (a6 % 256 ^ 8 + 2 ^ 64 * (a7 % 256 ^ 8 + 2 ^ 64 * 0)))))))  = P := by
  simp only [Nat.reducePow] at *
  omega


set_option exponentiation.threshold 600 in
/-- the result extraction of `MulDivOverflow`: eight quotient words at `sp - 136`. -/
theorem mdo_main (X Y D sp : Nat) (M : Janus.Arm64.Memory) (hsp : 136 ≤ sp) (hD : D ≠ 0)
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hq : wv M (sp - 136) 8 = X * Y / D) :
    (if (((M.readLE (sp - 96) 8 = 0 ∧ M.readLE (sp - 104) 8 = 0) ∧ M.readLE (sp - 88) 8 = 0) ∧ M.readLE (sp - 80) 8 = 0)
      then 0#8 else 1#8).toNat = (muldivOv X Y D).toNat ∧
    M.readLE (sp - 136) 8 + 2 ^ 64 * M.readLE (sp - 128) 8 + 2 ^ 128 * M.readLE (sp - 120) 8 +
      2 ^ 192 * M.readLE (sp - 112) 8 = muldivSpec X Y D := by
  have e1 : sp - 136 + 8 = sp - 128 := by omega
  have e2 : sp - 128 + 8 = sp - 120 := by omega
  have e3 : sp - 120 + 8 = sp - 112 := by omega
  have e4 : sp - 112 + 8 = sp - 104 := by omega
  have e5 : sp - 104 + 8 = sp - 96 := by omega
  have e6 : sp - 96 + 8 = sp - 88 := by omega
  have e7 : sp - 88 + 8 = sp - 80 := by omega
  simp only [wv, e1, e2, e3, e4, e5, e6, e7] at hq
  have b0 := Janus.Arm64.Memory.readLE_lt M (sp - 136) 8
  have b1 := Janus.Arm64.Memory.readLE_lt M (sp - 128) 8
  have b2 := Janus.Arm64.Memory.readLE_lt M (sp - 120) 8
  have b3 := Janus.Arm64.Memory.readLE_lt M (sp - 112) 8
  have b4 := Janus.Arm64.Memory.readLE_lt M (sp - 104) 8
  have b5 := Janus.Arm64.Memory.readLE_lt M (sp - 96) 8
  have b6 := Janus.Arm64.Memory.readLE_lt M (sp - 88) 8
  have b7 := Janus.Arm64.Memory.readLE_lt M (sp - 80) 8
  have hQ : X * Y / D < 2 ^ 512 := by
    have h1 : X * Y / D ≤ X * Y := Nat.div_le_self _ _
    have h2 := Nat.mul_lt_mul'' hX hY
    omega
  simp only [muldivOv, muldivSpec, if_neg hD]
  simp only [Nat.reducePow] at *
  constructor
  · by_cases h : (((M.readLE (sp - 96) 8 = 0 ∧ M.readLE (sp - 104) 8 = 0) ∧ M.readLE (sp - 88) 8 = 0) ∧ M.readLE (sp - 80) 8 = 0)
    · rw [if_pos h]
      have : ¬ (115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ X * Y / D) := by
        obtain ⟨⟨⟨h5, h4⟩, h6⟩, h7⟩ := h
        omega
      simp [this]
    · rw [if_neg h]
      have : 115792089237316195423570985008687907853269984665640564039457584007913129639936 ≤ X * Y / D := by
        rcases Nat.lt_or_ge (X * Y / D) 115792089237316195423570985008687907853269984665640564039457584007913129639936 with hc | hc
        · exfalso
          apply h
          omega
        · exact hc
      simp [this]
  · omega


theorem lsb_w64 (w : Nat) : (BitVec.ofNat 64 w).getLsbD 0 = decide (w % 2 = 1) := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]
  simp [Nat.testBit_zero]

theorem lsb_w32 (w : Nat) : (BitVec.setWidth 32 (BitVec.ofNat 64 w)).getLsbD 0 = decide (w % 2 = 1) := by
  rw [BitVec.getLsbD_eq_getElem (by decide)]
  rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp [Nat.testBit_zero, Nat.mod_mod_of_dvd]

theorem shr1_w64 (w : Nat) (hw : w < 2 ^ 64) : (BitVec.ofNat 64 w >>> 1) = BitVec.ofNat 64 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

<<<<<<< HEAD

/-- three 16-byte zero stores at `p`, `p+16`, `p+24` clear five words -/
theorem wv_zero5 (m : Janus.Arm64.Memory) (p q r : Nat) (h1 : q = p + 16) (h2 : r = p + 24) :
    wv (((m.writeLE p 16 0).writeLE q 16 0).writeLE r 16 0) p 5 = 0 := by
  subst h1 h2
  have e : ∀ a, p ≤ a → a + 8 ≤ p + 40 → (a - p) % 8 = 0 → (((m.writeLE p 16 0).writeLE (p + 16) 16 0).writeLE (p + 24) 16 0).readLE a 8 = 0 := by
    intro a h1 h2 h8
    rcases (by omega : a + 8 ≤ p + 16 ∨ (p + 16 ≤ a ∧ a + 8 ≤ p + 24) ∨ (p + 24 ≤ a ∧ a + 8 ≤ p + 40)) with h | h | h
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_inside _ _ h1 h]
      simp
    · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_inside _ _ h.1 (by omega)]
      simp
    · rw [Janus.Arm64.Memory.readLE_writeLE_inside _ _ h.1 h.2]
      simp
  simp only [wv, e p (by omega) (by omega) (by omega), e (p + 8) (by omega) (by omega) (by omega),
    e (p + 8 + 8) (by omega) (by omega) (by omega), e (p + 8 + 8 + 8) (by omega) (by omega) (by omega),
    e (p + 8 + 8 + 8 + 8) (by omega) (by omega) (by omega)]

theorem wv_zero5' (m : Janus.Arm64.Memory) (p q r : Nat) (h1 : q = p + 16) (h2 : r = p + 24) :
    wv (((m.writeLE p 16 (BitVec.toNat (0 : BitVec 128))).writeLE q 16 (BitVec.toNat (0 : BitVec 128))).writeLE r 16
      (BitVec.toNat (0 : BitVec 128))) p 5 = 0 := by
  have e : BitVec.toNat (0 : BitVec 128) = 0 := rfl
  rw [e]
  exact wv_zero5 m p q r h1 h2

=======
>>>>>>> fv/wd
end Fv256.F
