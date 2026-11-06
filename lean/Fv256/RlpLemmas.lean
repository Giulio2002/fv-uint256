import Fv256.RlpSpec

open Janus.Arm64

namespace Fv256.Rlp

theorem rlpVal_zero (m : Memory) : rlpVal m 0 = 0 := by simp [rlpVal]
theorem rlpVal_zero_bv (m : Memory) : rlpVal m (BitVec.toNat (0 : BitVec 64)) = 0 := by simp [rlpVal]
theorem rlpBytes_zero : rlpBytes 0 = [0x80] := by simp [rlpBytes]
theorem strBytes_write1 (m : Memory) (p v : Nat) : Janus.Spec.strBytes (m.writeLE p 1 v) p 1 = [v % 256] := by
  simp [Janus.Spec.strBytes, Janus.Arm64.Memory.bytes_writeLE]

end Fv256.Rlp
