import Fv256.RlpSpec

open Janus.Arm64

namespace Fv256.Rlp

theorem rlpVal_zero (m : Memory) : rlpVal m 0 = 0 := by simp [rlpVal]
theorem rlpVal_zero_bv (m : Memory) : rlpVal m (BitVec.toNat (0 : BitVec 64)) = 0 := by simp [rlpVal]
theorem rlpBytes_zero : rlpBytes 0 = [0x80] := by simp [rlpBytes]
theorem strBytes_write1 (m : Memory) (p v : Nat) : Janus.Spec.strBytes (m.writeLE p 1 v) p 1 = [v % 256] := by
  simp [Janus.Spec.strBytes, Janus.Arm64.Memory.bytes_writeLE]

theorem bitLen_le7_lt (v : Nat) (h0 : v ≠ 0) (h7 : Spec.bitLen v ≤ 7) : v < 128 := by
  simp only [Spec.bitLen, h0, ite_false] at h7
  exact (Nat.log2_lt h0).1 (show v.log2 < 7 by omega)

/-- the one-byte encoding: `0 < v`, `bitLen v ≤ 7` -/
theorem rlpBytes_small (v : Nat) (h0 : v ≠ 0) (h7 : Spec.bitLen v ≤ 7) : rlpBytes v = [v] := by
  simp [rlpBytes, h0, h7]

theorem bitLen_le_256 (v : Nat) (h : v < 2 ^ 256) : Spec.bitLen v ≤ 256 := by
  by_cases h0 : v = 0
  · simp [Spec.bitLen, h0]
  · simp only [Spec.bitLen, h0, ite_false]
    have := (Nat.log2_lt h0).2 h
    omega

theorem strBytes_write_out (m : Memory) (a k v p n : Nat) (h : a + k ≤ p ∨ p + n ≤ a) :
    Janus.Spec.strBytes (m.writeLE a k v) p n = Janus.Spec.strBytes m p n := by
  unfold Janus.Spec.strBytes
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Janus.Arm64.Memory.bytes_writeLE_outside (m := m) (by omega)]

theorem rlpVal_write_out (m : Memory) (a k v z : Nat) (h : a + k ≤ z ∨ z + 32 ≤ a) :
    rlpVal (m.writeLE a k v) z = rlpVal m z := by
  unfold rlpVal
  split
  · rfl
  · exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint (m := m) v (by omega)

end Fv256.Rlp
