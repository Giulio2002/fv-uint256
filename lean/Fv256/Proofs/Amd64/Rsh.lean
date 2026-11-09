import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).Rsh(x *Int, n uint) *Int` (amd64): `z = x >> n`

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) and every Go call state such that the return-address slot
is writable, the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` does not overlap the return-address
slot, and `z`, `x` are equal or disjoint, the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number
at `z` afterwards is `Fv256.Spec.rsh` of the number at `x`, shifted right by `n` (`RCX`, any 64-bit value), before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Wit.nonvacuous`: a concrete call satisfies the precondition; `Wit.returns`: it returns `z` holding the shifted value of `x`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Rsh

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

set_option maxHeartbeats 16000000 in
theorem correctness_proof (z x n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, n]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.rsh (valueAt s x 32) n.toNat ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint, Alias] at *
  rcases hzx with rfl | hzx
  · try simp only [Disjoint, Alias] at *
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
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
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
  · try simp only [Disjoint, Alias] at *
    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : n.toNat = m at *
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
              rw [Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem x.toNat), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shrd_val _ _ m ht (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 8)), Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
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
              rw [Util.shr_or_nat0 _ _ t ht1 ht (Util.readLE8_lt s.mem (x.toNat + 24)) (Util.readLE8_lt s.mem (x.toNat + 16))]
              rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24)))]
              simp only [Spec.rsh]
              exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              )
        · first
          | (exfalso; omega)
          | (
              by_cases hlt : m - 192 < 64
              · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
                have hq : 192 + t - 192 = t := (by omega)
                have hm : (192 + t) % 64 = t := (by omega)
                have hd : (s.mem.readLE (x.toNat + 24) 8) / 2 ^ t < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (x.toNat + 24))
                simp (disch := omega) only [hq, hm, ht, ite_true, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Util.and_ones_lt, Util.ones_and_lt]
                rw [Nat.mod_eq_of_lt hd]
                simp only [Spec.rsh]
                exact Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24))
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
          | (
              by_cases hlt : m - 192 < 64
              · obtain rfl : m = 192 := (by omega)
                simp (disch := omega) only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh, Nat.reduceSub, Nat.reduceLT, ite_true, Util.and_ones_lt, Util.ones_and_lt]
                (try rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (x.toNat + 24))])
                omega
              · simp only [if_neg hlt]
                simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.and_zero, Nat.zero_and, Nat.zero_or, Nat.or_zero, Spec.rsh]
                rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem x.toNat); have := (Util.readLE8_lt s.mem (x.toNat + 8)); have := (Util.readLE8_lt s.mem (x.toNat + 16)); have := (Util.readLE8_lt s.mem (x.toNat + 24)); omega) (by omega)]
                try omega
              )
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then n else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.rsh (valueAt s x 32) n.toNat ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, n, hret, setup, hpre,
    correctness_proof z x n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness_proof z x n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt]
  decide

end Wit

end Fv256.Amd64.Rsh
