import Fv256.Proofs.Arm64.SqrtProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.UtilF

/-!
# Library summaries of the callees of `Sqrt` (arm64): `(*Int).Lsh` (in place) and `(*Int).Rsh` for shift counts in `[33, 128]`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SqrtSum

abbrev sqrtEntry : Nat := segAddr Fv256.Arm64.SqrtProg.program "github.com/holiman/uint256.(*Int).Sqrt"
abbrev lshEntry : Nat := segAddr Fv256.Arm64.SqrtProg.program "github.com/holiman/uint256.(*Int).Lsh"
abbrev rshEntry : Nat := segAddr Fv256.Arm64.SqrtProg.program "github.com/holiman/uint256.(*Int).Rsh"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem lsh_summary :
    Summary Fv256.Arm64.SqrtProg.program lshEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        s.regs 1 = s.regs 0 ∧ 33 ≤ (s.regs 2).toNat ∧ (s.regs 2).toNat ≤ 128)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧ s'.regs 0 = s.regs 0 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Spec.lsh (s.mem.readLE (s.regs 0).toNat 32) (s.regs 2).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) := by
  intro s hpc ⟨h30a, h30b, hzb, hza, hzx, hn1, hn2⟩
  have hz0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have hz1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have hz2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have hz3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  janus_run [Util.readLE_32, hzx, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, by omega, by omega⟩
      have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega)
      have hp : (128 + t - 128) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem (s.regs 0).toNat)]
      simp only [Spec.lsh, Spec.W, Nat.reducePow]
      exact Util.lsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem (s.regs 0).toNat) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 24))
    · janus_frame
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      have ht1 : 1 ≤ m := (by omega)
      have ht : m < 64 := (by omega)
      have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)
      simp only [hc, Nat.mod_eq_of_lt ht]
      rw [Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem (s.regs 0).toNat), Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)), Util.shl_or_bv0 _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16))]
      simp only [Spec.lsh, Spec.W, Nat.reducePow]
      exact Util.lsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem (s.regs 0).toNat) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 24))
    · janus_frame
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, by omega, by omega⟩
      have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega)
      have hp : (64 + t - 64) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)), Util.shl_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem (s.regs 0).toNat)]
      simp only [Spec.lsh, Spec.W, Nat.reducePow]
      exact Util.lsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem (s.regs 0).toNat) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 0).toNat + 24))
    · janus_frame

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem rsh_summary :
    Summary Fv256.Arm64.SqrtProg.program rshEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        Disjoint32 (s.regs 0).toNat (s.regs 1).toNat ∧ 33 ≤ (s.regs 2).toNat ∧ (s.regs 2).toNat ≤ 128)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧ s'.regs 0 = s.regs 0 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Spec.rsh (s.mem.readLE (s.regs 1).toNat 32) (s.regs 2).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) := by
  intro s hpc ⟨h30a, h30b, hzb, hza, hxb, hxa, hzx, hn1, hn2⟩
  have hz0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hz1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hz2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hz3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  simp only [Disjoint32, Disjoint] at hzx
  janus_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 128 + t := ⟨m - 128, (by omega), (by omega)⟩
      have hc : 18446744073709551616 - (128 + t) - 18446744073709551424 = 64 - t := (by omega)
      have hp : (128 + t - 128) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh2_t _ _ _ _ t ht (Util.readLE8_lt s.mem (s.regs 1).toNat) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24))
    · janus_frame
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      have ht1 : 1 ≤ m := (by omega)
      have ht : m < 64 := (by omega)
      have hc : (18446744073709551616 - m - 18446744073709551552) % 64 = (64 - m) % 64 := (by omega)
      simp only [hc, Nat.mod_eq_of_lt ht]
      rw [Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)) (Util.readLE8_lt s.mem (s.regs 1).toNat), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)), Util.shr_or_nat _ _ m ht1 ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh0_t _ _ _ _ m ht (Util.readLE8_lt s.mem (s.regs 1).toNat) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24))
    · janus_frame
  · refine ⟨?_, ?_⟩
    · generalize hm : (s.regs 2).toNat = m at *
      obtain ⟨t, ht, rfl⟩ : ∃ t, t < 64 ∧ m = 64 + t := ⟨m - 64, (by omega), (by omega)⟩
      have hc : 18446744073709551616 - (64 + t) - 18446744073709551488 = 64 - t := (by omega)
      have hp : (64 + t - 64) % 64 = t := (by omega)
      simp only [hc, hp]
      rw [Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)), Util.shr_or_bv _ _ t ht (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)))]
      simp only [Spec.rsh]
      exact Util.rsh1_t _ _ _ _ t ht (Util.readLE8_lt s.mem (s.regs 1).toNat) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)) (Util.readLE8_lt s.mem ((s.regs 1).toNat + 24))
    · janus_frame

end Fv256.Arm64.SqrtSum
