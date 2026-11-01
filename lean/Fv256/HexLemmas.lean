import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# Hexadecimal parsing: architecture-independent lemmas (family C)

Lemmas about `parseHex` and the digit arithmetic shared by the arm64 and amd64 proofs of `SetFromHex`/`FromHex`/`MustFromHex`.
-/

open Janus Janus.Arm64 Fv256.C

namespace Fv256.C

/-- the byte sequence of the string -/
def bytesAt (m : Memory) (hp : Nat) : Nat → Nat := fun k => m.readLE (hp + k) 1

theorem allHex_join {b : Nat → Nat} {a c d : Nat} (h1 : allHex b a c) (h2 : allHex b c d) : allHex b a d := by
  intro k hk1 hk2
  by_cases h : k < c
  · exact h1 k hk1 h
  · exact h2 k (by omega) hk2

theorem allHex_step {b : Nat → Nat} {a r : Nat} (h : allHex b a r) (hr : (hexNib (b r)).isSome) :
    allHex b a (r + 1) := by
  intro k hk1 hk2
  by_cases h' : k < r
  · exact h k hk1 h'
  · have : k = r := by omega
    subst this; exact hr

theorem allHex_nil (b : Nat → Nat) (a : Nat) : allHex b a a := fun k h1 h2 => by omega

theorem hexNib_lt16 {c v : Nat} (h : hexNib c = some v) : v < 16 := by
  unfold hexNib at h
  by_cases h1 : 48 ≤ c ∧ c ≤ 57
  · simp [h1] at h; omega
  · by_cases h2 : 97 ≤ c ∧ c ≤ 102
    · simp [h1, h2] at h; omega
    · by_cases h3 : 65 ≤ c ∧ c ≤ 70
      · simp [h1, h2, h3] at h; omega
      · simp [h1, h2, h3] at h

theorem hexNib_none_of {c : Nat} (h : (hexNib c).getD 255 = 255) : hexNib c = none := by
  cases h' : hexNib c with
  | none => rfl
  | some v => rw [h'] at h; simp at h; have := hexNib_lt16 h'; omega

theorem hexNib_some_of {c : Nat} (h : (hexNib c).getD 255 ≠ 255) :
    (hexNib c).isSome = true ∧ (hexNib c).getD 255 = (hexNib c).getD 0 := by
  cases h' : hexNib c with
  | none => rw [h'] at h; simp at h
  | some v => simp


theorem hexNib_getD_lt (c : Nat) : (hexNib c).getD 255 < 256 := by
  cases h : hexNib c with
  | none => simp
  | some v => have := hexNib_lt16 h; simp; omega

theorem toInt_sub16 (e : Nat) (h : e < 2^32) : (BitVec.ofNat 64 e - 16#64).toInt = (e : Int) - 16 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_sub16 (e : Nat) (h : 16 ≤ e) (h2 : e < 2^32) : BitVec.ofNat 64 e - 16#64 = BitVec.ofNat 64 (e - 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_add1 (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sp_add16 (a t : BitVec 64) (h : a.toNat + 16 = t.toNat) : a + 16#64 = t := by
  apply BitVec.eq_of_toNat_eq
  have := t.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sp_sub24 (t : BitVec 64) (h : 24 ≤ t.toNat) : (t - 24#64).toNat = t.toNat - 24 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := t.isLt
  omega

theorem sw32 (N : Nat) (h : N < 256) : (BitVec.setWidth 32 (BitVec.ofNat 64 N)).toNat = N := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega


theorem toInt_sub16' (x : BitVec 64) (h : x.toNat < 2 ^ 32) : (x - 16#64).toInt = (x.toNat : Int) - 16 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_sub16' (x : BitVec 64) (h : 16 ≤ x.toNat) : x - 16#64 = BitVec.ofNat 64 (x.toNat - 16) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sp_sub16 (t : BitVec 64) (h : 16 ≤ t.toNat) : (t - 16#64).toNat = t.toNat - 16 := by
  have := t.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem zero_read (m : Memory) (z j : Nat) (hj : j < 4) :
    ((((m.writeLE (z + 16) 8 0).writeLE (z + 24) 8 0).writeLE z 8 0).writeLE (z + 8) 8 0).readLE (z + 8 * j) 8 = 0 := by
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [show z + 8 * 0 = z by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
  · rw [show z + 8 * 1 = z + 8 by omega, Memory.readLE_writeLE_self]
  · rw [show z + 8 * 2 = z + 16 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
  · rw [show z + 8 * 3 = z + 24 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]


theorem pe_empty (b : Nat → Nat) : parseHex b 0 = .error 0 := by
  unfold parseHex; simp

theorem pe_missing (b : Nat → Nat) (n : Nat) (hn : n ≠ 0) (h : n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) :
    parseHex b n = .error 1 := by
  unfold parseHex; rw [if_neg hn, if_pos h]

theorem pe_emptyNum (b : Nat → Nat) (n : Nat) (hn : n = 2) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) :
    parseHex b n = .error 2 := by
  subst hn; unfold parseHex
  have : ¬ (2 < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by decide), if_neg this, if_pos rfl]

theorem pe_lead (b : Nat → Nat) (n : Nat) (hn : 3 < n) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) (h2 : b 2 = 48) :
    parseHex b n = .error 3 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_pos ⟨hn, h2⟩]

theorem pe_big (b : Nat → Nat) (n : Nat) (hn : 66 < n) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) (h2 : b 2 ≠ 48) :
    parseHex b n = .error 4 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_neg (by omega), if_pos hn]

open Classical in
theorem pe_body (b : Nat → Nat) (n : Nat) (hn : 3 ≤ n) (hn2 : n ≤ 66) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88)
    (h2 : 3 < n → b 2 ≠ 48) :
    parseHex b n = if allHex b 2 n then Except.ok (hexSum b 2 (n - 2)) else Except.error 5 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  have h3 : ¬ (3 < n ∧ b 2 = 48) := fun ⟨a, c⟩ => h2 a c
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_neg h3, if_neg (by omega)]


theorem hexSum_congr (b b' : Nat → Nat) (a : Nat) :
    ∀ n, (∀ k, a ≤ k → k < a + n → b k = b' k) → hexSum b a n = hexSum b' a n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [hexSum, hexDigit]
    rw [ih (fun k h1 h2 => h k h1 (by omega)), h (a + n) (by omega) (by omega)]

open Classical in
theorem parseHex_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) :
    parseHex b n = parseHex b' n := by
  have hall : allHex b 2 n ↔ allHex b' 2 n := by
    constructor
    · intro H k h1 h2; rw [← h k h2]; exact H k h1 h2
    · intro H k h1 h2; rw [h k h2]; exact H k h1 h2
  unfold parseHex
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · subst h1; simp
  have e0 : b 0 = b' 0 := h 0 (by omega)
  have e1 : b 1 = b' 1 := h 1 (by omega)
  by_cases h2 : n = 2
  · subst h2; simp [e0, e1]
  have e2 : b 2 = b' 2 := h 2 (by omega)
  simp only [e0, e1, e2, hall]
  rw [hexSum_congr b b' 2 (n - 2) (fun k h1 h2 => h k (by omega))]

open Classical in
theorem parseHex_error_lt (b : Nat → Nat) (n e : Nat) (h : parseHex b n = Except.error e) : e < 6 := by
  unfold parseHex at h
  by_cases h0 : n = 0
  · rw [if_pos h0] at h; cases h; decide
  rw [if_neg h0] at h
  by_cases h1 : n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)
  · rw [if_pos h1] at h; cases h; decide
  rw [if_neg h1] at h
  by_cases h2 : n = 2
  · rw [if_pos h2] at h; cases h; decide
  rw [if_neg h2] at h
  by_cases h3 : 3 < n ∧ b 2 = 48
  · rw [if_pos h3] at h; cases h; decide
  rw [if_neg h3] at h
  by_cases h4 : 66 < n
  · rw [if_pos h4] at h; cases h; decide
  rw [if_neg h4] at h
  by_cases h5 : allHex b 2 n
  · rw [if_pos h5] at h; cases h
  · rw [if_neg h5] at h; cases h; decide


end Fv256.C
