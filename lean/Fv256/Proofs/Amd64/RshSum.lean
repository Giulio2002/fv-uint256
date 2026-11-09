import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.RshProg

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RshSum

abbrev rshEntry : Nat := segAddr Fv256.RshProg.program "github.com/holiman/uint256.(*Int).Rsh"

/-- `Rsh(z, x, n)` as a callee (`z` in `RAX`, `x` in `RBX`, `n` in `RCX`, return address at `[RSP]`), `z`, `x` disjoint 32-byte
objects, the return-address slot disjoint from `z`. Library summary over `Fv256.RshProg.program` (no `Extracted`). -/
theorem rsh_summary (z x : BitVec 64) :
    Summary Fv256.RshProg.program rshEntry
      (fun s => s.regs 0 = z ∧ s.regs 3 = x ∧ s.xmm 15 = 0 ∧
        (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Disjoint z 32 (s.regs 4) 8 ∧ Disjoint z 32 x 32)
      (fun s s' => s'.regs 0 = z ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        valueAt s' z 32 = Spec.rsh (valueAt s x 32) (s.regs 1).toNat ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)]) := by
  intro s hpc ⟨hz0, hx0, hx15, ⟨hra1, hra2⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at *
  simp only [valueAt, Disjoint] at *
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, hx15]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (
  · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); generalize hm : (s.regs 1).toNat = m at *
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
  )

end Fv256.Amd64.RshSum
