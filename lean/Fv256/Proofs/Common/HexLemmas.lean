import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Spec.HexLemmas

/-!
# Hexadecimal parsing: architecture-independent lemmas (family C)

Lemmas about `parseHex` and the digit arithmetic shared by the arm64 and amd64 proofs of `SetFromHex`/`FromHex`/`MustFromHex`.
-/

open Janus Janus.Arm64 Fv256.C

namespace Fv256.C

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


theorem cmp255 (N : Nat) (hN : N < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 N))) - 255#8 = 0#8) ↔ N = 255 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    simp at this
    omega
  · intro h; subst h; decide

theorem cmp120 (N : Nat) (hN : N < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 N))) - 120#8 = 0#8) ↔ N = 120 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    simp at this
    omega
  · intro h; subst h; decide

theorem cmp88 (N : Nat) (hN : N < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 N))) - 88#8 = 0#8) ↔ N = 88 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    simp at this
    omega
  · intro h; subst h; decide

theorem zero_read16 (m : Memory) (z j : Nat) (hj : j < 4) :
    (((m.writeLE (z + 16) 16 0).writeLE z 16 0).readLE (z + 8 * j) 8) = 0 := by
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [show z + 8 * 0 = z by omega, Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]; simp
  · rw [Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]; simp
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]; simp
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]; simp

theorem digit_limb (a c t : Nat) (ha : a < 2 ^ 64) (ht : t < 16) :
    (a + 2 ^ 64 * c) / 16 ^ t % 16 = a / 16 ^ t % 16 := by
  have hp : 0 < 16 ^ t := Nat.pow_pos (by decide)
  have h3 : (2 : Nat) ^ 64 = 16 ^ t * (16 * 16 ^ (15 - t)) := by
    have e : (16 : Nat) ^ (t + ((15 - t) + 1)) = 16 ^ t * (16 ^ (15 - t) * 16) := by
      rw [Nat.pow_add, Nat.pow_succ]
    have e2 : t + ((15 - t) + 1) = 16 := by omega
    rw [e2] at e
    have e3 : (16 : Nat) ^ 16 = 2 ^ 64 := by decide
    rw [← e3, e, Nat.mul_comm (16 ^ (15 - t)) 16]
  have h5 : (a + 2 ^ 64 * c) = a + 16 ^ t * (16 * (16 ^ (15 - t) * c)) := by
    rw [h3, Nat.mul_assoc, Nat.mul_assoc]
  rw [h5, Nat.add_mul_div_left _ _ hp, Nat.add_mul_mod_self_left]

theorem dig_limb (z0 z1 z2 z3 w t : Nat) (h0 : z0 < 2 ^ 64) (h1 : z1 < 2 ^ 64) (h2 : z2 < 2 ^ 64) (hw : w < 4) (ht : t < 16) :
    (z0 + 2 ^ 64 * z1 + 2 ^ 128 * z2 + 2 ^ 192 * z3) / 16 ^ (16 * w + t) % 16 =
      (if w = 0 then z0 else if w = 1 then z1 else if w = 2 then z2 else z3) / 16 ^ t % 16 := by
  have e16 : ∀ k, (16 : Nat) ^ (16 * k + t) = 2 ^ (64 * k) * 16 ^ t := by
    intro k
    rw [Nat.pow_add, show (16 : Nat) ^ (16 * k) = 2 ^ (64 * k) by
      rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]; congr 1; omega]
  rw [e16, ← Nat.div_div_eq_div_mul]
  obtain rfl | rfl | rfl | rfl : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 := by omega
  · have : z0 + 2 ^ 64 * z1 + 2 ^ 128 * z2 + 2 ^ 192 * z3 = z0 + 2 ^ 64 * (z1 + 2 ^ 64 * (z2 + 2 ^ 64 * z3)) := by omega
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, if_true]
    rw [this]; exact digit_limb _ _ _ h0 ht
  · have : (z0 + 2 ^ 64 * z1 + 2 ^ 128 * z2 + 2 ^ 192 * z3) / 2 ^ (64 * 1) = z1 + 2 ^ 64 * (z2 + 2 ^ 64 * z3) := by omega
    rw [this]; simp only [show (1 : Nat) ≠ 0 by decide, if_false, if_true]; exact digit_limb _ _ _ h1 ht
  · have : (z0 + 2 ^ 64 * z1 + 2 ^ 128 * z2 + 2 ^ 192 * z3) / 2 ^ (64 * 2) = z2 + 2 ^ 64 * z3 := by omega
    rw [this]; simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false, if_true]
    exact digit_limb _ _ _ h2 ht
  · have : (z0 + 2 ^ 64 * z1 + 2 ^ 128 * z2 + 2 ^ 192 * z3) / 2 ^ (64 * 3) = z3 := by omega
    rw [this]; simp only [show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, if_false]

theorem bl_bounds (v : Nat) : v < 2 ^ Spec.bitLen v ∧ (v = 0 ∨ 2 ^ (Spec.bitLen v - 1) ≤ v) := by
  by_cases h : v = 0
  · subst h; simp [Spec.bitLen]
  · unfold Spec.bitLen; rw [if_neg h]
    refine ⟨Nat.lt_log2_self, Or.inr ?_⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.log2_self_le h

/-- the number of hexadecimal digits of `v` (at least one) is `n`: `16^(n-1) ≤ v < 16^n` (or `n = 1`) -/
theorem nib_spec (v n : Nat) (hn : n = max 1 ((Spec.bitLen v + 3) / 4)) : hexDigits v n := by
  unfold hexDigits
  obtain ⟨h1, h2⟩ := bl_bounds v
  have h16 : ∀ k, (16 : Nat) ^ k = 2 ^ (4 * k) := fun k => by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
  refine ⟨by omega, ?_, ?_⟩
  · rw [h16]
    refine Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) ?_)
    omega
  · by_cases hn1 : n = 1
    · exact Or.inl hn1
    · right
      rw [h16]
      rcases h2 with h2 | h2
      · subst h2; simp [Spec.bitLen] at hn; omega
      · refine Nat.le_trans (Nat.pow_le_pow_right (by decide) ?_) h2
        omega

theorem rot_mod16 (x r : Nat) (hx : x < 2 ^ 64) (hr : r ≤ 60) :
    ((BitVec.ofNat 64 x).rotateRight r).toNat % 16 = x / 2 ^ r % 16 := by
  rw [BitVec.toNat_rotateRight]
  have h16 : (16 : Nat) = 2 ^ 4 := rfl
  rw [h16, Nat.or_mod_two_pow]
  have hr64 : r % 64 = r := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, hr64, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hb : (x * 2 ^ (64 - r) % 2 ^ 64) % 2 ^ 4 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (by
      rw [show (2:Nat)^64 = 2^4 * 2^60 by rw [← Nat.pow_add]]
      exact Nat.dvd_mul_right _ _)]
    have : 2 ^ 4 ∣ 2 ^ (64 - r) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans this (Nat.dvd_mul_left _ _))
  rw [hb]; simp

theorem nib_mask (a M : Nat) (hM : M % 16 = 15) : (a &&& M) % 16 = a % 16 := by
  have h16 : (16 : Nat) = 2 ^ 4 := rfl
  rw [h16] at hM ⊢
  rw [Nat.and_mod_two_pow, hM]
  have : (a % 2 ^ 4) < 2 ^ 4 := Nat.mod_lt _ (by decide)
  have h15 : (15 : Nat) = 2 ^ 4 - 1 := rfl
  rw [h15]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow this

theorem nibB (x r M : Nat) (hx : x < 2 ^ 64) (hr : r ≤ 60) (hM : M % 16 = 15) :
    (((BitVec.ofNat 64 x).rotateRight r).toNat &&& M) % 16 = x / 2 ^ r % 16 := by
  rw [nib_mask _ _ hM, rot_mod16 x r hx hr]

theorem hexChar_lt (d : Nat) (hd : d < 16) : hexChar d < 256 := by
  unfold hexChar; split <;> omega

theorem sel_limb (m : Nat → Nat) (k : Nat) (hk : k < 4) :
    (if k = 0 then m 0 else if k = 1 then m 8 else if k = 2 then m 16 else m 24) = m (8 * k) := by
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals simp

theorem hc_mod (d : Nat) (hd : d < 16) : hexChar d % 18446744073709551616 % 256 ^ 1 = hexChar d := by
  have := hexChar_lt d hd
  have h1 : hexChar d % 18446744073709551616 = hexChar d := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.pow_one]
  exact Nat.mod_eq_of_lt this

def st16 (M : Memory) (b y : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Nat) : Memory :=
  (((((((((((((((M.writeLE (b + (y + 2)) 1 v0).writeLE (b + (y + 3)) 1 v1).writeLE (b + (y + 4)) 1 v2).writeLE (b + (y + 5)) 1 v3).writeLE (b + (y + 6)) 1 v4).writeLE (b + (y + 7)) 1 v5).writeLE (b + (y + 8)) 1 v6).writeLE (b + (y + 9)) 1 v7).writeLE (b + (y + 10)) 1 v8).writeLE (b + (y + 11)) 1 v9).writeLE (b + (y + 12)) 1 v10).writeLE (b + (y + 13)) 1 v11).writeLE (b + (y + 14)) 1 v12).writeLE (b + (y + 15)) 1 v13).writeLE (b + (y + 16)) 1 v14).writeLE (b + (y + 17)) 1 v15

theorem st16_out (M : Memory) (b y : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Nat) (a n : Nat)
    (h : a + n ≤ b + y + 2 ∨ b + y + 18 ≤ a) :
    (st16 M b y v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).readLE a n = M.readLE a n := by
  unfold st16
  repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem st16_get (M : Memory) (b y : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Nat) (t : Nat) (ht : t < 16) :
    (st16 M b y v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).readLE (b + y + 2 + t) 1 = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15].getD t 0 % 256 ^ 1 := by
  unfold st16
  have e : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 ∨ t = 13 ∨ t = 14 ∨ t = 15 := by omega
  rcases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 0 = b + (y + 2) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 1 = b + (y + 3) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 2 = b + (y + 4) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 3 = b + (y + 5) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 4 = b + (y + 6) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 5 = b + (y + 7) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 6 = b + (y + 8) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 7 = b + (y + 9) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 8 = b + (y + 10) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 9 = b + (y + 11) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 10 = b + (y + 12) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 11 = b + (y + 13) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 12 = b + (y + 14) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 13 = b + (y + 15) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [show b + y + 2 + 14 = b + (y + 16) by omega, Memory.readLE_writeLE_self]
    rfl
  · rw [show b + y + 2 + 15 = b + (y + 17) by omega, Memory.readLE_writeLE_self]
    rfl

theorem st16_frame {m M : Memory} {rs : List (Nat × Nat)} (b y : Nat) (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Nat)
    (h : MemFrame m M rs) (r : Nat × Nat) (hr : r ∈ rs) (h1 : r.1 ≤ b + y + 2) (h2 : b + y + 18 ≤ r.2) :
    MemFrame m (st16 M b y v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) rs := by
  unfold st16
  exact ((((((((((((((((h.writeLE v0 hr (by omega) (by omega)).writeLE v1 hr (by omega) (by omega)).writeLE v2 hr (by omega) (by omega)).writeLE v3 hr (by omega) (by omega)).writeLE v4 hr (by omega) (by omega)).writeLE v5 hr (by omega) (by omega)).writeLE v6 hr (by omega) (by omega)).writeLE v7 hr (by omega) (by omega)).writeLE v8 hr (by omega) (by omega)).writeLE v9 hr (by omega) (by omega)).writeLE v10 hr (by omega) (by omega)).writeLE v11 hr (by omega) (by omega)).writeLE v12 hr (by omega) (by omega)).writeLE v13 hr (by omega) (by omega)).writeLE v14 hr (by omega) (by omega)).writeLE v15 hr (by omega) (by omega))

theorem iter_vals (x : Nat) (hx : x < 2 ^ 64) :
  [
    hexChar (((BitVec.ofNat 64 x).rotateRight 60).toNat % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 56).toNat &&& 18446744073709551375) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 52).toNat &&& 18446744073709547535) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 48).toNat &&& 18446744073709486095) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 44).toNat &&& 18446744073708503055) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 40).toNat &&& 18446744073692774415) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 36).toNat &&& 18446744073441116175) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 32).toNat &&& 18446744069414584335) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 28).toNat &&& 18446744004990074895) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 24).toNat &&& 18446742974197923855) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 20).toNat &&& 18446726481523507215) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 16).toNat &&& 18446462598732840975) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 12).toNat &&& 18442240474082181135) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 8).toNat &&& 18374686479671623695) % 16) % 18446744073709551616,
    hexChar ((((BitVec.ofNat 64 x).rotateRight 4).toNat &&& 17293822569102704655) % 16) % 18446744073709551616,
    hexChar (x % 16) % 18446744073709551616]
  = (List.range 16).map (fun t => hexChar (x / 16 ^ (15 - t) % 16)) := by
  simp only [List.range, List.range.loop, List.map]
  have e0 : ((BitVec.ofNat 64 x).rotateRight 60).toNat % 16 = x / 16 ^ 15 % 16 := by
    rw [rot_mod16 x 60 hx (by omega)]
  have e1 : (((BitVec.ofNat 64 x).rotateRight 56).toNat &&& 18446744073709551375) % 16 = x / 16 ^ 14 % 16 := by
    rw [nibB x 56 _ hx (by omega) (by decide)]
  have e2 : (((BitVec.ofNat 64 x).rotateRight 52).toNat &&& 18446744073709547535) % 16 = x / 16 ^ 13 % 16 := by
    rw [nibB x 52 _ hx (by omega) (by decide)]
  have e3 : (((BitVec.ofNat 64 x).rotateRight 48).toNat &&& 18446744073709486095) % 16 = x / 16 ^ 12 % 16 := by
    rw [nibB x 48 _ hx (by omega) (by decide)]
  have e4 : (((BitVec.ofNat 64 x).rotateRight 44).toNat &&& 18446744073708503055) % 16 = x / 16 ^ 11 % 16 := by
    rw [nibB x 44 _ hx (by omega) (by decide)]
  have e5 : (((BitVec.ofNat 64 x).rotateRight 40).toNat &&& 18446744073692774415) % 16 = x / 16 ^ 10 % 16 := by
    rw [nibB x 40 _ hx (by omega) (by decide)]
  have e6 : (((BitVec.ofNat 64 x).rotateRight 36).toNat &&& 18446744073441116175) % 16 = x / 16 ^ 9 % 16 := by
    rw [nibB x 36 _ hx (by omega) (by decide)]
  have e7 : (((BitVec.ofNat 64 x).rotateRight 32).toNat &&& 18446744069414584335) % 16 = x / 16 ^ 8 % 16 := by
    rw [nibB x 32 _ hx (by omega) (by decide)]
  have e8 : (((BitVec.ofNat 64 x).rotateRight 28).toNat &&& 18446744004990074895) % 16 = x / 16 ^ 7 % 16 := by
    rw [nibB x 28 _ hx (by omega) (by decide)]
  have e9 : (((BitVec.ofNat 64 x).rotateRight 24).toNat &&& 18446742974197923855) % 16 = x / 16 ^ 6 % 16 := by
    rw [nibB x 24 _ hx (by omega) (by decide)]
  have e10 : (((BitVec.ofNat 64 x).rotateRight 20).toNat &&& 18446726481523507215) % 16 = x / 16 ^ 5 % 16 := by
    rw [nibB x 20 _ hx (by omega) (by decide)]
  have e11 : (((BitVec.ofNat 64 x).rotateRight 16).toNat &&& 18446462598732840975) % 16 = x / 16 ^ 4 % 16 := by
    rw [nibB x 16 _ hx (by omega) (by decide)]
  have e12 : (((BitVec.ofNat 64 x).rotateRight 12).toNat &&& 18442240474082181135) % 16 = x / 16 ^ 3 % 16 := by
    rw [nibB x 12 _ hx (by omega) (by decide)]
  have e13 : (((BitVec.ofNat 64 x).rotateRight 8).toNat &&& 18374686479671623695) % 16 = x / 16 ^ 2 % 16 := by
    rw [nibB x 8 _ hx (by omega) (by decide)]
  have e14 : (((BitVec.ofNat 64 x).rotateRight 4).toNat &&& 17293822569102704655) % 16 = x / 16 ^ 1 % 16 := by
    rw [nibB x 4 _ hx (by omega) (by decide)]
  have e15 : x % 16 = x / 16 ^ 0 % 16 := by simp
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  have hm' : ∀ n, hexChar (n % 16) % 18446744073709551616 = hexChar (n % 16) := fun n =>
    Nat.mod_eq_of_lt (by have := hexChar_lt (n % 16) (Nat.mod_lt _ (by decide)); omega)
  simp [hm']

theorem st16_regions (M : Memory) (b y v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Nat) :
    (st16 M b y v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).regions = M.regions := rfl

end Fv256.C
