import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.By1Loop

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.DivWork

namespace Fv256.Amd64.DivWork2

theorem by1_summary :
    Summary Extracted.program by1
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        StackGuardOK s 0 ∧ StackWritable s 16 40 ∧
        2 ≤ (s.regs 6).toNat ∧ (s.regs 6).toNat < 2 ^ 20 ∧ 2 ^ 63 ≤ (s.regs 9).toNat ∧
        (s.regs 6).toNat - 1 ≤ (s.regs 3).toNat ∧
        Buffer s (s.regs 0) (8 * ((s.regs 6).toNat - 1)) true ∧ Buffer s (s.regs 7) (8 * (s.regs 6).toNat) false ∧
        ((s.regs 0).toNat + 8 * ((s.regs 6).toNat - 1) ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * ((s.regs 6).toNat - 1) ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * (s.regs 6).toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 40 ≤ (s.regs 7).toNat) ∧
        s.mem.readLE ((s.regs 7).toNat + 8 * ((s.regs 6).toNat - 1)) 8 < (s.regs 9).toNat)
      (fun s s' => ∃ (rem' : Nat) (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        s' = { s with regs := R', rip := retAddrOf s, flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 rem' ∧ R' 4 = s.regs 4 + 8 ∧ R' 8 = BitVec.ofNat 64 (s.regs 0).toNat ∧
        (∀ i, i ∉ [0, 1, 2, 4, 6, 8, 10, 11, 12] → R' i = s.regs i) ∧
        rem' < (s.regs 9).toNat ∧
        Fv256.B.wv s.mem (s.regs 7).toNat (s.regs 6).toNat =
          (s.regs 9).toNat * Fv256.B.wv M' (s.regs 0).toNat ((s.regs 6).toNat - 1) + rem' ∧
        MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 6).toNat - 1)),
          ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16),
          ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hg, ⟨hlow, hnw, hacc⟩, hn1, hn2, hd1, hql, ⟨hqw, hq⟩, ⟨huw, hu⟩, hqu, hqs, hus, htop⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgr hgb hgl hnw2 hacc hlow hnw
  have hcode := by1Head_lt
  have hd2 : (s.regs 9).toNat < 2 ^ 64 := (s.regs 9).isLt
  have hdivlt : ¬ (18446744073709551616 ≤ ((18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + 18446744073709551615) / BitVec.toNat (s.regs 9)) := by
    have hd2' := (s.regs 9).isLt
    refine Nat.not_le.mpr (Nat.div_lt_of_lt_mul ?_)
    have : (18446744073709551615 - BitVec.toNat (s.regs 9) + 1) * 18446744073709551616 ≤ BitVec.toNat (s.regs 9) * 18446744073709551616 :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at this
    rw [Nat.mul_comm (BitVec.toNat (s.regs 9))]
    omega
  janus64_run [BitVec.toNat_not, hdivlt] until [by1Head]
  have hd2' := (s.regs 9).isLt
  have hvlt : ((18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + 18446744073709551615) / BitVec.toNat (s.regs 9) < 2 ^ 64 :=
    Nat.lt_of_not_ge hdivlt
  have hvrel : ((18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + 18446744073709551615) / BitVec.toNat (s.regs 9) + 2 ^ 64 =
      (2 ^ 64 * 2 ^ 64 - 1) / BitVec.toNat (s.regs 9) := by
    have hd0 : 0 < BitVec.toNat (s.regs 9) := by omega
    have e : (2 ^ 64 * 2 ^ 64 - 1 : Nat) = (18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + 18446744073709551615 +
        BitVec.toNat (s.regs 9) * 18446744073709551616 := by
      have : (BitVec.toNat (s.regs 9)) * 18446744073709551616 ≤ 2 ^ 64 * 2 ^ 64 - 1 := by
        have := Nat.mul_le_mul_right 18446744073709551616 (show BitVec.toNat (s.regs 9) ≤ 18446744073709551615 by omega)
        omega
      have e2 : (18446744073709551615 - BitVec.toNat (s.regs 9)) * 18446744073709551616 + BitVec.toNat (s.regs 9) * 18446744073709551616 = 18446744073709551615 * 18446744073709551616 := by
        rw [← Nat.add_mul]; congr 1; omega
      omega
    rw [e, Nat.mul_comm (BitVec.toNat (s.regs 9)) 18446744073709551616, Nat.add_mul_div_right _ _ hd0]
  refine Fv256.Amd64.DivWork.by1_loop s (s.regs 0).toNat (s.regs 7).toNat (s.regs 6).toNat (s.regs 9).toNat _ hn1 hn2 hd1 hd2 hvrel rfl rfl hql rfl
    hq hqw hu huw hqu hqs hus (by omega) hnw (Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)) hra2 ((s.regs 6).toNat - 1) (s.mem.readLE ((s.regs 7).toNat + 8 * ((s.regs 6).toNat - 1)) 8) _ _ _ (Nat.le_refl _) ?hrem ?r0 ?r1 ?r2 ?r4 ?r5 ?r8 ?ru ?hI ?hu ?hfr ?hrbp
  case hrem => exact htop
  case r0 => simp [setRegF]
  case r1 =>
    have e : (s.regs 7).toNat + (s.regs 6).toNat * 8 - 8 = (s.regs 7).toNat + 8 * ((s.regs 6).toNat - 1) := by omega
    simp [setRegF, e]
  case r2 =>
    simp only [setRegF]; simp
    bv_omega
  case r4 => simp [setRegF]
  case r5 => simp [setRegF]
  case r8 => simp [setRegF]
  case ru =>
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setRegF]
    repeat' rw [if_neg (by omega)]
  case hI =>
    rw [show (s.regs 6).toNat - ((s.regs 6).toNat - 1) = 1 by omega, show (s.regs 6).toNat - 1 - ((s.regs 6).toNat - 1) = 0 by omega]
    simp [Fv256.B.wv]
  case hu =>
    intro i hi
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case hfr =>
    exact (((MemFrame.refl _ _).writeLE _ (r := ((s.regs 4).toNat - 8, (s.regs 4).toNat)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)) (by simp) (by omega) (by omega)).writeLE _
      (r := ((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)) (by simp) (by omega) (by omega)
  case hrbp =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt

end Fv256.Amd64.DivWork2
