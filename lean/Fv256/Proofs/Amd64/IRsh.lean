import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).IRsh(n uint) *Int` (amd64): in place, `z = z >> n`

**Guarantee.** For every pointer `z` (receiver, `RAX`), every shift count `n` (`RBX`, any 64-bit value; counts of 256 or more
give zero) and every Go call state such that the stack-growth check falls through (`StackGuardOK s 0`), the window
`[SP-40, SP+8)` (the 32-byte frame, the saved frame pointer and the callee's return address, plus the caller's return-address
slot) is writable, the 32 bytes at `z` are writable and do not overlap the frame window: the call returns (no fault, no panic),
obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.rsh` of the number at `z` before the call, shifted
by `n`, and no byte outside `z[0..32)` and the frame window `[SP-40, SP)` changes (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IRsh

set_option maxHeartbeats 16000000 in
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.rsh (valueAt s z 32) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 40) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hds
  simp only [valueAt, Disjoint] at *
  try simp only [Disjoint, Alias] at *
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]
  · refine ⟨?_, ?_⟩
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); generalize hm : n.toNat = m at *
      rcases (show m = 0 ∨ (0 < m ∧ m < 64) ∨ m = 64 ∨ (64 < m ∧ m < 128) ∨ m = 128 ∨ (128 < m ∧ m < 192) ∨ 192 ≤ m by omega) with h | h | h | h | h | h | h
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 0 := (by omega)
            simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
            )
      · first
        | (exfalso; omega)
        | (
            have ht : m < 64 := (by omega)
            simp only [Nat.mod_eq_of_lt ht]
            rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem z.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 64 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (64 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (64 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551488 + (64 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            obtain rfl : m = 128 := (by omega)
            simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false]
            omega
            )
      · first
        | (exfalso; omega)
        | (
            obtain ⟨t, ht1, ht, rfl⟩ : ∃ t, 1 ≤ t ∧ t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega), (by omega)⟩
            have hs : (18446744073709551616 - (128 + t)) % 64 = 64 - t := (by omega)
            have hm64 : (128 + t) % 64 = t := (by omega)
            have hc : 18446744073709551616 - (18446744073709551424 + (128 + t)) < 64 := (by omega)
            simp only [hs, hm64, hc, ite_true]
            simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
            rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
            rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
            simp only [Spec.rsh]
            exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            )
      · first
        | (exfalso; omega)
        | (
            by_cases hlt : m - 192 < 64
            · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
              have hq : 192 + t - 192 = t := (by omega)
              have hm : (192 + t) % 64 = t := (by omega)
              have hd : (s.mem.readLE (z.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24))
              simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
              rw [Nat.mod_eq_of_lt hd]
              simp only [Spec.rsh]
              exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
        | (
            by_cases hlt : m - 192 < 64
            · obtain rfl : m = 192 := (by omega)
              simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
              (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24))])
              omega
            · simp only [if_neg hlt]
              simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
              rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
              try omega
            )
    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then n else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 z 32 true ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ z.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.rsh (valueAt s z 32) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 40 :=
  ⟨ret, s0, z, n, hret, setup, hpre,
    correctness z n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Spec.rsh]
  decide

end Witness

end Fv256.Amd64.IRsh
