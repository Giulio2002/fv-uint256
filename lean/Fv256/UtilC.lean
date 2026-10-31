import Fv256.SpecC
import Fv256.Util

namespace Fv256.C

theorem bigAbs_mod_aux (w : Nat → Nat) (k : Nat) :
    bigAbs w (4 + k) % 2 ^ 256 = bigAbs w 4 % 2 ^ 256 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (bigAbs w (4 + k) + w (4 + k) * 2 ^ (64 * (4 + k))) % 2 ^ 256 = _
    have : 2 ^ (64 * (4 + k)) = 2 ^ 256 * 2 ^ (64 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [this, show w (4 + k) * (2 ^ 256 * 2 ^ (64 * k)) = 2 ^ 256 * (w (4 + k) * 2 ^ (64 * k)) by rw [Nat.mul_left_comm],
      Nat.add_mul_mod_self_left]
    exact ih

theorem bigAbs_mod (w : Nat → Nat) (n : Nat) (h : 4 ≤ n) :
    bigAbs w n % 2 ^ 256 = bigAbs w 4 % 2 ^ 256 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 + k := ⟨n - 4, by omega⟩
  exact bigAbs_mod_aux w k

theorem ov_flag (n : Nat) :
    (if (n : Int) ≤ 4 then (0#64 : BitVec 64) else 1#64).toNat = if decide (4 < n) = true then 1 else 0 := by
  by_cases h : n ≤ 4
  · have : ¬ 4 < n := by omega
    have h2 : (n : Int) ≤ 4 := by omega
    simp [h2, this]
  · have h1 : ¬ (n : Int) ≤ 4 := by omega
    have : 4 < n := by omega
    simp [h1, this]

theorem ov_flag' (n : Nat) :
    (if (n : Int) ≤ 4 then (0#64 : BitVec 64) else 1#64).toNat = if 4 < n then 1 else 0 := by
  have := ov_flag n
  simpa using this

/-- the low byte of `RAX` after `SETG AL` when the flag is zero -/
theorem lowbyte0 (z : BitVec 64) : (z &&& 18446744073709551360#64 ||| 0#64).toNat % 256 = 0 := by
  rw [BitVec.or_zero, BitVec.toNat_and]
  have h : (18446744073709551360#64).toNat = 2^64 - 2^8 := by decide
  rw [h]
  show (z.toNat &&& (2^64 - 2^8)) % 2^8 = 0
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and]
  by_cases hi : i < 8
  · have : (2^64 - 2^8 : Nat).testBit i = false := by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with h|h|h|h|h|h|h|h <;> subst h <;> decide
    simp [this]
  · simp [hi]

theorem ov8 (n : Nat) :
    (if 4 < (n : Int) then (1#8 : BitVec 8) else 0#8).toNat = (fromBigOv n).toNat := by
  by_cases h : 4 < n
  · have h2 : 4 < (n : Int) := by omega
    simp [h2, fromBigOv, h]
  · have h2 : ¬ 4 < (n : Int) := by omega
    simp [h2, fromBigOv, h]


/-! ## `big.Int` magnitude facts -/

theorem bigAbs_congr (w w' : Nat → Nat) (n : Nat) (h : ∀ i, i < n → w i = w' i) : bigAbs w n = bigAbs w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bigAbs]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem bigAbs_lt (w : Nat → Nat) (hw : ∀ i, w i < 2 ^ 64) (n : Nat) : bigAbs w n < 2 ^ (64 * n) := by
  induction n with
  | zero => simp [bigAbs]
  | succ n ih =>
    simp only [bigAbs]
    have h1 := hw n
    have h2 : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1 <;> omega
    rw [h2]
    have h3 : w n * 2 ^ (64 * n) + 2 ^ (64 * n) ≤ 2 ^ (64 * n) * 2 ^ 64 := by
      have : (w n + 1) * 2 ^ (64 * n) ≤ 2 ^ 64 * 2 ^ (64 * n) := Nat.mul_le_mul_right _ h1
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ 64)] at this
      exact this
    omega

theorem bigAbs_ge (w : Nat → Nat) (n : Nat) (hn : 0 < n) (hlast : w (n - 1) ≠ 0) :
    2 ^ (64 * (n - 1)) ≤ bigAbs w n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [bigAbs, Nat.add_sub_cancel] at *
  have : 1 * 2 ^ (64 * m) ≤ w m * 2 ^ (64 * m) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem bigAbs_pos (w : Nat → Nat) (n : Nat) (hn : 0 < n) (hlast : w (n - 1) ≠ 0) : 0 < bigAbs w n := by
  have := bigAbs_ge w n hn hlast
  have : 0 < 2 ^ (64 * (n - 1)) := Nat.two_pow_pos _
  omega

theorem bigAbs_big (w : Nat → Nat) (n : Nat) (hn : 4 < n) (hlast : w (n - 1) ≠ 0) :
    2 ^ 256 ≤ bigAbs w n := by
  have h := bigAbs_ge w n (by omega) hlast
  have : 2 ^ 256 ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem bigAbs_small (w : Nat → Nat) (hw : ∀ i, w i < 2 ^ 64) (n : Nat) (hn : n ≤ 4) : bigAbs w n < 2 ^ 256 := by
  have h := bigAbs_lt w hw n
  have : 2 ^ (64 * n) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ## the specification of `CmpBig`, unfolded -/

theorem cmpBig_neg (z abs : Nat) (h : 0 < abs) : cmpBig z (bigVal true abs) = 1 := by
  simp only [cmpBig, bigVal, if_true]
  have : ¬ ((z : Int) < -(abs : Int)) := by omega
  have h2 : ¬ ((z : Int) = -(abs : Int)) := by omega
  simp [this, h2]

theorem cmpBig_big (z abs : Nat) (hz : z < abs) : cmpBig z (bigVal false abs) = -1 := by
  simp only [cmpBig, bigVal]
  have : (z : Int) < (abs : Int) := by omega
  simp [this]

theorem cmpBig_core (z abs len : Nat) (negb : Bool) (hz : z < 2 ^ 256) (hn : ¬ (negb = true ∧ len ≠ 0))
    (hl : len ≤ 4) (hlt : abs < 2 ^ 256) (h0 : len = 0 → abs = 0) :
    Spec.cmp z (fromBig negb abs) = cmpBig z (bigVal negb abs) := by
  cases negb
  · simp only [fromBig, bigVal, Bool.false_eq_true, if_false, cmpBig, Spec.cmp, Spec.W]
    rw [Nat.mod_eq_of_lt hlt]
    by_cases h1 : z < abs
    · have : (z : Int) < abs := by omega
      simp [h1, this]
    · by_cases h2 : z = abs
      · subst h2; simp
      · have : ¬ (z : Int) < abs := by omega
        have h3 : ¬ (z : Int) = abs := by omega
        simp [h1, h2, this, h3]
  · have hl0 : len = 0 := by
      by_cases h : len = 0
      · exact h
      · exact absurd ⟨rfl, h⟩ hn
    have ha := h0 hl0
    subst ha
    simp only [fromBig, bigVal, if_true, cmpBig, Spec.cmp, Spec.neg, Spec.W]
    have e : (2 ^ 256 - 0 % 2 ^ 256) % 2 ^ 256 = 0 := by decide
    rw [e]
    by_cases h1 : z < 0
    · omega
    · by_cases h2 : z = 0
      · subst h2; simp
      · have : ¬ (z : Int) < -((0 : Nat) : Int) := by omega
        have h3 : ¬ (z : Int) = -((0 : Nat) : Int) := by omega
        simp [h1, h2, this, h3]


theorem lsb0 (x : BitVec 64) : x.getLsbD 0 = decide (x.toNat % 2 = 1) := by
  simp [BitVec.getLsbD, Nat.testBit_zero]

theorem ofNat_sub8 (x : BitVec 64) (h : 8 ≤ x.toNat) : BitVec.ofNat 64 (x.toNat - 8) = x - 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]
  omega

theorem bit1 (a : Nat) (h : a < 2) (h2 : a % 2 = 1) : a = 1 := by omega

theorem noov_of (r : BitVec 64) (ov : Bool) (h : r.toNat = if ov = true then 1 else 0)
    (hb : (r.getLsbD 0 == false) = true) : ov = false := by
  cases ov
  · rfl
  · simp only [if_true] at h
    rw [lsb0] at hb
    simp [h] at hb

theorem ov_of (r : BitVec 64) (ov : Bool) (h : r.toNat = if ov = true then 1 else 0)
    (hb : ¬ (r.getLsbD 0 == false) = true) : ov = true := by
  cases ov
  · simp only [Bool.false_eq_true, if_false] at h
    rw [lsb0] at hb
    simp [h] at hb
  · rfl

theorem ovF (n : Nat) (h : fromBigOv n = false) : n ≤ 4 := by
  simp only [fromBigOv] at h
  simpa using h

theorem ovT (n : Nat) (h : fromBigOv n = true) : 4 < n := by
  simp only [fromBigOv] at h
  simpa using h

theorem bit0 (a : Nat) (h : a < 2) (h2 : ¬ a % 2 = 1) : (a == 1) = false := by
  have : a ≠ 1 := by omega
  simpa using this

/-- the stack stores of `CmpBig`'s prologue and the zeroing of its local `Int` do not touch the words of the `big.Int` -/
theorem bigAbs_stackframe (m : Janus.Arm64.Memory) (sp ret z pw len : Nat) (h1 : 72 ≤ sp)
    (h2 : pw + 8 * len ≤ sp - 72 ∨ sp - 72 + 88 ≤ pw) :
    bigAbs (fun i =>
      (((((((m.writeLE (sp - 64) 8 ret).writeLE (sp - 72) 8 (sp - 8)).writeLE (sp + 8) 8 z).writeLE (sp - 40) 8 0).writeLE
        (sp - 32) 8 0).writeLE (sp - 24) 8 0).writeLE (sp - 16) 8 0).readLE (pw + 8 * i) 8) len =
    bigAbs (fun i => m.readLE (pw + 8 * i) 8) len := by
  apply bigAbs_congr
  intro i hi
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]

open Janus.Amd64 in
theorem ite_sub (c : Prop) [Decidable c] :
    (if c then (18446744073709551615#64 : BitVec 64) else 0#64) = (subFlags (0#64) (0#64) (decide c)).fst := by
  by_cases h : c <;> simp [h, subFlags]

theorem sw8_iff (r : BitVec 64) : (BitVec.setWidth 8 r = 0#8) ↔ r.toNat % 256 = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_setWidth] using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_setWidth] using h

theorem noov_of64 (r : BitVec 64) (ov : Bool) (h : r.toNat % 256 = ov.toNat)
    (hb : BitVec.setWidth 8 r = 0#8) : ov = false := by
  rw [sw8_iff] at hb
  cases ov
  · rfl
  · simp at h; omega

theorem ov_of64 (r : BitVec 64) (ov : Bool) (h : r.toNat % 256 = ov.toNat)
    (hb : ¬ BitVec.setWidth 8 r = 0#8) : ov = true := by
  rw [sw8_iff] at hb
  cases ov
  · simp at h; omega
  · rfl

theorem bit0_8 (a : Nat) (h : a < 2) (hb : BitVec.ofNat 8 a = 0#8) : (a == 1) = false := by
  have : a ≠ 1 := by
    intro e; subst e; revert hb; decide
  simpa using this

theorem bit1_8 (a : Nat) (h : a < 2) (hb : ¬ BitVec.ofNat 8 a = 0#8) : (a == 1) = true := by
  have : a = 1 := by
    rcases (by omega : a = 0 ∨ a = 1) with e | e
    · subst e; exact absurd (by decide) hb
    · exact e
  simpa using this

theorem bigAbs_stackframe64 (m : Janus.Arm64.Memory) (sp bp z v1 v2 c pw len : Nat) (h1 : 72 ≤ sp)
    (h2 : pw + 8 * len ≤ sp - 72 ∨ sp + 16 ≤ pw) :
    bigAbs (fun i =>
      (((((m.writeLE (sp - 8) 8 bp).writeLE (sp + 8) 8 z).writeLE (sp - 40) 16 v1).writeLE (sp - 24) 16 v2).writeLE
        (sp - 64) 8 c).readLE (pw + 8 * i) 8) len =
    bigAbs (fun i => m.readLE (pw + 8 * i) 8) len := by
  apply bigAbs_congr
  intro i hi
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]


theorem bigAbs_write (m : Janus.Arm64.Memory) (a v pw len : Nat) (h : pw + 8 * len ≤ a ∨ a + 8 ≤ pw) :
    bigAbs (fun i => (m.writeLE a 8 v).readLE (pw + 8 * i) 8) len = bigAbs (fun i => m.readLE (pw + 8 * i) 8) len := by
  apply bigAbs_congr
  intro i hi
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem bigAbs_frame (m0 m1 : Janus.Arm64.Memory) (rs : List (Nat × Nat)) (pw len : Nat)
    (hf : Janus.MemFrame m0 m1 rs) (ho : Janus.Outside pw (8 * len) rs) :
    bigAbs (fun i => m1.readLE (pw + 8 * i) 8) len = bigAbs (fun i => m0.readLE (pw + 8 * i) 8) len := by
  apply bigAbs_congr
  intro i hi
  exact hf.readLE _ _ (Janus.Outside.of_sub ho (by omega) (by omega))

theorem flag_false (r : BitVec 64) (ov : Bool) (h : r.toNat = if ov = true then 1 else 0)
    (hb : (r.getLsbD 0 == true) = true) : ov = true := by
  cases ov
  · simp only [Bool.false_eq_true, if_false] at h
    rw [lsb0] at hb
    simp [h] at hb
  · rfl

theorem flag_true (r : BitVec 64) (ov : Bool) (h : r.toNat = if ov = true then 1 else 0)
    (hb : ¬ (r.getLsbD 0 == true) = true) : ov = false := by
  cases ov
  · rfl
  · simp only [if_true] at h
    rw [lsb0] at hb
    simp [h] at hb

theorem ovFalse_of (n : Nat) (h : n ≤ 4) : fromBigOv n = false := by
  simp only [fromBigOv]; simpa using h

theorem ovTrue_of (n : Nat) (h : 4 < n) : fromBigOv n = true := by
  simp only [fromBigOv]; simpa using h

theorem ovF_of (n : Nat) (h : fromBigOv n = false) : n ≤ 4 := ovF n h

/-! ## A witness memory holding a `big.Int` (shared by the SetFromBig / CmpBig / FromBig witnesses)

`z = DST` (32 bytes), `b = DST + 32` is `big.Int{neg = true, abs = nat{ptr = DST + 64, len = 2, cap = 2}}`,
and the two words at `DST + 64` are `5` and `1`: the number `-(5 + 2^64)`. -/
section Wit
open Janus.Contracts.EqHashModel Janus.Arm64

def bigBase : Nat := DST + 32
def bigWords : Nat := DST + 64

def bigEntries : List (Nat × Nat) :=
  [(bigBase, 1), (bigBase + 8, 0x40), (bigBase + 9, 0x08), (bigBase + 10, 0x03),
    (bigBase + 16, 2), (bigBase + 24, 2), (bigWords, 5), (bigWords + 8, 1)]

theorem bigEntries_none (a : Nat) (h : a < 0x30000) : bigEntries.lookup a = none := by
  unfold bigEntries bigBase bigWords Janus.Contracts.EqHashModel.DST
  have e : ∀ k, 0x30000 ≤ k → (a == k) = false := fun k hk => by
    simp only [beq_eq_false_iff_ne]; omega
  simp only [List.lookup, e 198688 (by decide), e 198696 (by decide), e 198697 (by decide), e 198698 (by decide),
    e 198704 (by decide), e 198712 (by decide), e 198720 (by decide), e 198728 (by decide)]

def bigTable : List (Nat × Nat) :=
  Janus.Contracts.EqHashModel.wtable ++ bigEntries

def bigMem : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((bigTable.lookup a).getD 0), Janus.Contracts.EqHashModel.wmem.regions⟩

def bigMem64 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((Janus.Contracts.IfaceModel.wsp + 2, 0x20) :: bigTable).lookup a).getD 0),
    Janus.Contracts.EqHashModel.wmem.regions⟩

end Wit

end Fv256.C
