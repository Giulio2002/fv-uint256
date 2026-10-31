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

/-! ## A witness memory holding a `big.Int` (shared by the SetFromBig / CmpBig / FromBig witnesses)

`z = DST` (32 bytes), `b = DST + 32` is `big.Int{neg = true, abs = nat{ptr = DST + 64, len = 2, cap = 2}}`,
and the two words at `DST + 64` are `5` and `1`: the number `-(5 + 2^64)`. -/
section Wit
open Janus.Contracts.EqHashModel Janus.Arm64

def bigBase : Nat := DST + 32
def bigWords : Nat := DST + 64

def bigTable : List (Nat × Nat) :=
  Janus.Contracts.EqHashModel.wtable ++ [(bigBase, 1), (bigBase + 8, 0x40), (bigBase + 9, 0x08), (bigBase + 10, 0x03),
    (bigBase + 16, 2), (bigBase + 24, 2), (bigWords, 5), (bigWords + 8, 1)]

def bigMem : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((bigTable.lookup a).getD 0), Janus.Contracts.EqHashModel.wmem.regions⟩

def bigMem64 : Memory :=
  ⟨fun a => BitVec.ofNat 8 ((((Janus.Contracts.IfaceModel.wsp + 2, 0x20) :: bigTable).lookup a).getD 0),
    Janus.Contracts.EqHashModel.wmem.regions⟩

end Wit

end Fv256.C
