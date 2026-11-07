import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).ISRsh(n uint) *Int` (arm64): in place arithmetic shift right, `z = z >> n` (sign-propagating)

**Guarantee.** For every pointer `z` (receiver, `X0`) and shift count `n` (`X1`, any 64-bit value), every Go call whose
stack-growth check falls through (`GuardOK s 56`: covers the check of `ISRsh` and of the `SRsh` it calls) and whose stack window
`[SP-112, SP)` (the frames of `ISRsh` and `SRsh`) is writable and aligned (`StackOK s 112 0`): if the 32 bytes at `z` are writable and
do not overlap the stack window, and the goroutine's stack-guard word (`g.stackguard0`) is not inside that window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z`
afterwards is `Fv256.Spec.srsh` of the number at `z` before the call (the two's-complement reading shifted right by `n` with sign
fill; counts of 256 or more give 0 or all ones), and no byte changes outside `z[0..32)` and the stack window
(`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISRsh

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => GuardOK s 56 ∧ StackOK s 112 0 ∧ Ptr32 s.mem z true ∧
        Disjoint z.toNat 32 (s.sp.toNat - 112) 112 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.srsh (val256 s.mem z.toNat) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 112) 112) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, hd1, hdg⟩
  janus_intro hs
  simp only [Disjoint] at *
  janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
  · rename_i _ hsg
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    rw [Util.srsh_pos _ _ (by have := Util.readLE8_lt s.mem (z.toNat + 24); omega)]
    generalize hm : n.toNat = m at *
    obtain rfl : m = 0 := (by omega)
    simp only [Spec.rsh, Nat.pow_zero, Nat.div_one]
  · rename_i _ hsg _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    rw [Util.srsh_pos _ _ (by have := Util.readLE8_lt s.mem (z.toNat + 24); omega)]
    generalize hm : n.toNat = m at *
    by_cases hlt : m - 192 < 64
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
      have hq : 192 + t - 192 = t := (by omega)
      simp only [hq, Nat.mod_eq_of_lt ht, ht, ite_true, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      simp only [Spec.rsh]
      rw [Nat.mod_eq_of_lt (Util.readLE8_lt s.mem (z.toNat + 24)), Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))]
    · simp only [if_neg hlt]
      simp only [Spec.rsh]
      rw [Util.rsh_big _ _ (by have := (Util.readLE8_lt s.mem z.toNat); have := (Util.readLE8_lt s.mem (z.toNat + 8)); have := (Util.readLE8_lt s.mem (z.toNat + 16)); have := (Util.readLE8_lt s.mem (z.toNat + 24)); omega) (by omega)]
      simp
  · rename_i _ hsg _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    rw [Util.srsh_pos _ _ (by have := Util.readLE8_lt s.mem (z.toNat + 24); omega)]
    generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega)
    have hp : (128 + t - 128) % 64 = t := (by omega)
    simp only [hc, hp]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
  · rename_i _ hsg _ _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    rw [Util.srsh_pos _ _ (by have := Util.readLE8_lt s.mem (z.toNat + 24); omega)]
    generalize hm : n.toNat = m at *
    have ht1 : 1 ≤ m := (by omega)
    have ht : m < 64 := (by omega)
    have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)
    simp only [hc, Nat.mod_eq_of_lt ht]
    rw [Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem z.toNat), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
  · rename_i _ hsg _ _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    rw [Util.srsh_pos _ _ (by have := Util.readLE8_lt s.mem (z.toNat + 24); omega)]
    generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega)
    have hp : (64 + t - 64) % 64 = t := (by omega)
    simp only [hc, hp]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem (z.toNat + 24)))]
    simp only [Spec.rsh]
    exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
  · rename_i _ hsg
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    obtain rfl : m = 0 := (by clear hsg; omega)
    rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]
    simp only [Nat.sub_zero, Nat.pow_zero, Nat.div_one, Nat.sub_self, Nat.add_zero]
  · rename_i _ hsg _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    rw [Util.srsh_neg_big _ _ (by omega) (by omega) (by omega)]
  · rename_i _ hsg _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 192 + t := ⟨m - 192, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (192 + t) - 18446744073709551360 = 64 - t := Util.sub_aux 192 t ht (by omega)
    have hp : (192 + t - 192) % 64 = t := (by clear hsg; omega)
    have hq : (192 + t) % 64 = t := (by clear hsg; omega)
    have hc1 : (18446744073709551616 - t + 64) % 18446744073709551616 = 64 - t := (by clear hsg; omega)
    have hc2 : 18446744073709551616 - t - 18446744073709551552 = 64 - t := Util.sub_aux2 t ht
    simp only [hp, hq, hc1, hc2, hc]
    rw [Util.top_val _ t (Util.readLE8_lt s.mem (z.toNat + 24)) ht]
    rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]
    have e := Util.rsh3_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
    rw [show 256 - (192 + t) = 64 - t from (by omega), ← e]
    have hP := Util.pw_le t (by omega)
    simp only [Nat.reducePow]
    generalize s.mem.readLE (z.toNat + 8) 8 * 2 ^ (64 - t) % 18446744073709551616 = w1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 * 2 ^ (64 - t) % 18446744073709551616 = w2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 * 2 ^ (64 - t) % 18446744073709551616 = w3 at *
    generalize s.mem.readLE z.toNat 8 / 2 ^ t = q0 at *
    generalize s.mem.readLE (z.toNat + 8) 8 / 2 ^ t = q1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 / 2 ^ t = q2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 / 2 ^ t = q3 at *
    generalize 2 ^ (64 - t) = P at *
    omega
  · rename_i _ hsg _ _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := Util.sub_aux 128 t ht (by omega)
    have hp : (128 + t - 128) % 64 = t := (by clear hsg; omega)
    have hq : (128 + t) % 64 = t := (by clear hsg; omega)
    have hc1 : (18446744073709551616 - t + 64) % 18446744073709551616 = 64 - t := (by clear hsg; omega)
    have hc2 : 18446744073709551616 - t - 18446744073709551552 = 64 - t := Util.sub_aux2 t ht
    simp only [hp, hq, hc1, hc2, hc]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Util.top_val _ t (Util.readLE8_lt s.mem (z.toNat + 24)) ht]
    rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]
    have e := Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
    rw [show 256 - (128 + t) = 64 + (64 - t) from (by omega), Nat.pow_add 2 64 (64 - t), ← e]
    have hP := Util.pw_le t (by omega)
    simp only [Nat.reducePow]
    generalize s.mem.readLE (z.toNat + 8) 8 * 2 ^ (64 - t) % 18446744073709551616 = w1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 * 2 ^ (64 - t) % 18446744073709551616 = w2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 * 2 ^ (64 - t) % 18446744073709551616 = w3 at *
    generalize s.mem.readLE z.toNat 8 / 2 ^ t = q0 at *
    generalize s.mem.readLE (z.toNat + 8) 8 / 2 ^ t = q1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 / 2 ^ t = q2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 / 2 ^ t = q3 at *
    generalize 2 ^ (64 - t) = P at *
    omega
  · rename_i _ hsg _ _ _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    have ht1 : 1 ≤ m := (by omega)
    have ht : m < 64 := (by clear hsg; omega)
    have hc2 : 18446744073709551616 - m - 18446744073709551552 = 64 - m := (by clear hsg; omega)
    simp only [hc2, Nat.mod_eq_of_lt ht]
    rw [Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem z.toNat), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Util.top_val _ m (Util.readLE8_lt s.mem (z.toNat + 24)) ht]
    rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]
    have e := Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
    rw [show 256 - m = 192 + (64 - m) from (by omega), Nat.pow_add, ← e]
    have hP := Util.pw_le m (by omega)
    simp only [Nat.reducePow]
    generalize s.mem.readLE (z.toNat + 8) 8 * 2 ^ (64 - m) % 18446744073709551616 = w1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 * 2 ^ (64 - m) % 18446744073709551616 = w2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 * 2 ^ (64 - m) % 18446744073709551616 = w3 at *
    generalize s.mem.readLE z.toNat 8 / 2 ^ m = q0 at *
    generalize s.mem.readLE (z.toNat + 8) 8 / 2 ^ m = q1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 / 2 ^ m = q2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 / 2 ^ m = q3 at *
    generalize 2 ^ (64 - m) = P at *
    omega
  · rename_i _ hsg _ _ _ _
    have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); 
    refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
    have hs3 : 9223372036854775808 ≤ s.mem.readLE (z.toNat + 24) 8 := by omega
    generalize hm : n.toNat = m at *
    obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩
    have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := Util.sub_aux 64 t ht (by omega)
    have hp : (64 + t - 64) % 64 = t := (by clear hsg; omega)
    have hq : (64 + t) % 64 = t := (by clear hsg; omega)
    have hc1 : (18446744073709551616 - t + 64) % 18446744073709551616 = 64 - t := (by clear hsg; omega)
    have hc2 : 18446744073709551616 - t - 18446744073709551552 = 64 - t := Util.sub_aux2 t ht
    simp only [hp, hq, hc1, hc2, hc]
    rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 8)), Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem (z.toNat + 16))]
    rw [Util.top_val _ t (Util.readLE8_lt s.mem (z.toNat + 24)) ht]
    rw [Util.srsh_neg _ _ (by omega) (by omega) (by omega)]
    have e := Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24))
    rw [show 256 - (64 + t) = 128 + (64 - t) from (by omega), Nat.pow_add 2 128 (64 - t), ← e]
    have hP := Util.pw_le t (by omega)
    simp only [Nat.reducePow]
    generalize s.mem.readLE (z.toNat + 8) 8 * 2 ^ (64 - t) % 18446744073709551616 = w1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 * 2 ^ (64 - t) % 18446744073709551616 = w2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 * 2 ^ (64 - t) % 18446744073709551616 = w3 at *
    generalize s.mem.readLE z.toNat 8 / 2 ^ t = q0 at *
    generalize s.mem.readLE (z.toNat + 8) 8 / 2 ^ t = q1 at *
    generalize s.mem.readLE (z.toNat + 16) 8 / 2 ^ t = q2 at *
    generalize s.mem.readLE (z.toNat + 24) 8 / 2 ^ t = q3 at *
    generalize 2 ^ (64 - t) = P at *
    omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }


theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 56 ∧ StackOK s0 112 0 ∧ Ptr32 s0.mem z true ∧ Disjoint z.toNat 32 (s0.sp.toNat - 112) 112 ∧
    Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 112) 112 :=
  ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, by unfold Disjoint; decide,
    by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (GuardOK s 56 ∧ StackOK s 112 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 112) 112 ∧
      Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 112) 112) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.srsh (val256 s.mem z.toNat) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 112) 112 :=
  ⟨ret, s0, z, n, hret, setup, hpre,
    correctness z n ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.ISRsh
