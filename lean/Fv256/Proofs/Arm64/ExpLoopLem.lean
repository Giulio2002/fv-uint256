import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.UtilF

namespace Fv256.Arm64.ExpLoopLem

theorem lsr1_gen (x : BitVec 64) :
    x.rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = x >>> 1 := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_rotateRight, BitVec.getElem_ushiftRight]
  have c1 : (18446744073709551615#64)[i] = true := by
    rw [BitVec.getElem_eq_testBit_toNat]
    simp only [BitVec.toNat_ofNat]
    rw [show (18446744073709551615:Nat) % 2^64 = 2^64-1 by decide, Nat.testBit_two_pow_sub_one]; simp [hi]
  have c2 : (9223372036854775807#64)[i] = decide (i < 63) := by
    rw [BitVec.getElem_eq_testBit_toNat]
    simp only [BitVec.toNat_ofNat]
    rw [show (9223372036854775807:Nat) % 2^64 = 2^63-1 by decide, Nat.testBit_two_pow_sub_one]
  rw [c1, c2]
  by_cases h : i < 63
  · simp [h, Nat.add_comm]
    rw [BitVec.getLsbD_eq_getElem (by omega)]
  · have : i = 63 := by omega
    subst this; simp

theorem lsr1 (w : Nat) (hw : w < 2 ^ 64) :
    (BitVec.ofNat 64 w).rotateRight 1 &&& 18446744073709551615#64 &&& 9223372036854775807#64 = BitVec.ofNat 64 (w / 2) := by
  rw [lsr1_gen, Fv256.F.shr1_w64 w hw]

theorem inc1 (k : Nat) : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod]

end Fv256.Arm64.ExpLoopLem
