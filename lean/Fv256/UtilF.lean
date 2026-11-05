import Fv256.UtilB
import Fv256.UdivremMath

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

end Fv256.F
