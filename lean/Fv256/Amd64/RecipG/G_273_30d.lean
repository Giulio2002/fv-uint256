import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_273_30d (s : State) (y3 : Nat) (x273rax x273rcx x273rbx x273rsi x273rdi x273r8 x273r10 x273r11 x273r12 x273r13 x273r15 x273mb0 x273mb8 x273m100 x273m208 x273m210 x273m218 x273m220 : Nat) (S' : State) : Prop :=
  ∃ x30dr12 x30dm68 x30dm70 x30dme8 x30dmf0 x30dmf8 x30dm1c0 x30dm1c8 x30dm1d0 x30dm1d8 x30dm1e0 x30dm1e8 x30dm1f0 x30dm1f8 x30dm200, L30d s S' x273rcx x273rbx x273rsi x273r10 x273r11 x30dr12 x273r13 x273r15 x30dm68 x30dm70 x273mb0 x273mb8 x30dme8 x30dmf0 x30dmf8 x273m100 x30dm1c0 x30dm1c8 x30dm1d0 x30dm1d8 x30dm1e0 x30dm1e8 x30dm1f0 x30dm1f8 x30dm200 x273m208 x273m210 x273m218 x273m220 ∧ x30dr12 = (x273rdi * x273r10 / 18446744073709551616) % 18446744073709551616 ∧ x30dm68 = (x273r8 * x273r12 / 18446744073709551616) % 18446744073709551616 ∧ x30dm70 = (x273rax * x273rbx) % 18446744073709551616 ∧ x30dme8 = (x273rdi * x273rbx / 18446744073709551616) % 18446744073709551616 ∧ x30dmf0 = (x273r8 * x273rbx / 18446744073709551616) % 18446744073709551616 ∧ x30dmf8 = (x273rax * x273rbx / 18446744073709551616) % 18446744073709551616 ∧ x30dm1c0 = (x273r12 * x273rsi) % 18446744073709551616 ∧ x30dm1c8 = (x273r12 * x273rsi / 18446744073709551616) % 18446744073709551616 ∧ x30dm1d0 = (x273rdi * x273r10) % 18446744073709551616 ∧ x30dm1d8 = (x273rdi * x273rbx) % 18446744073709551616 ∧ x30dm1e0 = (x273r12 * x273rdi) % 18446744073709551616 ∧ x30dm1e8 = (x273r12 * x273rdi / 18446744073709551616) % 18446744073709551616 ∧ x30dm1f0 = (x273r8 * x273r10) % 18446744073709551616 ∧ x30dm1f8 = (x273r8 * x273r10 / 18446744073709551616) % 18446744073709551616 ∧ x30dm200 = (x273r8 * x273rbx) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_273_30d {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x273)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x273rax x273rcx x273rbx x273rsi x273rdi x273r8 x273r10 x273r11 x273r12 x273r13 x273r15 x273mb0 x273mb8 x273m100 x273m208 x273m210 x273m218 x273m220 : Nat) (hL : L273 s S x273rax x273rcx x273rbx x273rsi x273rdi x273r8 x273r10 x273r11 x273r12 x273r13 x273r15 x273mb0 x273mb8 x273m100 x273m208 x273m210 x273m218 x273m220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x30d)) S (P_273_30d s y3 x273rax x273rcx x273rbx x273rsi x273rdi x273r8 x273r10 x273r11 x273r12 x273r13 x273r15 x273mb0 x273mb8 x273m100 x273m208 x273m210 x273m218 x273m220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x273rax, hB_x273rax, hE_x273rcx, hB_x273rcx, hE_x273rbx, hB_x273rbx, hE_x273rsi, hB_x273rsi, hE_x273rdi, hB_x273rdi, hE_x273r8, hB_x273r8, hE_x273r10, hB_x273r10, hE_x273r11, hB_x273r11, hE_x273r12, hB_x273r12, hE_x273r13, hB_x273r13, hE_x273r15, hB_x273r15, hE_x273mb0, hB_x273mb0, hE_x273mb8, hB_x273mb8, hE_x273m100, hB_x273m100, hE_x273m208, hB_x273m208, hE_x273m210, hB_x273m210, hE_x273m218, hB_x273m218, hE_x273m220, hB_x273m220⟩ := hL
  janus64_run [Util.readLE_32, hE_x273rax, hE_x273rcx, hE_x273rbx, hE_x273rsi, hE_x273rdi, hE_x273r8, hE_x273r10, hE_x273r11, hE_x273r12, hE_x273r13, hE_x273r15, hE_x273mb0, hE_x273mb8, hE_x273m100, hE_x273m208, hE_x273m210, hE_x273m218, hE_x273m220, hsp4, Nat.mod_eq_of_lt hB_x273rax, Nat.mod_eq_of_lt hB_x273rcx, Nat.mod_eq_of_lt hB_x273rbx, Nat.mod_eq_of_lt hB_x273rsi, Nat.mod_eq_of_lt hB_x273rdi, Nat.mod_eq_of_lt hB_x273r8, Nat.mod_eq_of_lt hB_x273r10, Nat.mod_eq_of_lt hB_x273r11, Nat.mod_eq_of_lt hB_x273r12, Nat.mod_eq_of_lt hB_x273r13, Nat.mod_eq_of_lt hB_x273r15, Nat.mod_eq_of_lt hB_x273mb0, Nat.mod_eq_of_lt hB_x273mb8, Nat.mod_eq_of_lt hB_x273m100, Nat.mod_eq_of_lt hB_x273m208, Nat.mod_eq_of_lt hB_x273m210, Nat.mod_eq_of_lt hB_x273m218, Nat.mod_eq_of_lt hB_x273m220]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (
  unfold P_273_30d
  refine ⟨(x273rdi * x273r10 / 18446744073709551616) % 18446744073709551616, (x273r8 * x273r12 / 18446744073709551616) % 18446744073709551616, (x273rax * x273rbx) % 18446744073709551616, (x273rdi * x273rbx / 18446744073709551616) % 18446744073709551616, (x273r8 * x273rbx / 18446744073709551616) % 18446744073709551616, (x273rax * x273rbx / 18446744073709551616) % 18446744073709551616, (x273r12 * x273rsi) % 18446744073709551616, (x273r12 * x273rsi / 18446744073709551616) % 18446744073709551616, (x273rdi * x273r10) % 18446744073709551616, (x273rdi * x273rbx) % 18446744073709551616, (x273r12 * x273rdi) % 18446744073709551616, (x273r12 * x273rdi / 18446744073709551616) % 18446744073709551616, (x273r8 * x273r10) % 18446744073709551616, (x273r8 * x273r10 / 18446744073709551616) % 18446744073709551616, (x273r8 * x273rbx) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L30d
    and_intros
    · first | exact hE_x273rcx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273rcx)
    · exact hB_x273rcx
    · first | exact hE_x273rbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273rbx)
    · exact hB_x273rbx
    · first | exact hE_x273rsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273rsi)
    · exact hB_x273rsi
    · first | exact hE_x273r10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273r10)
    · exact hB_x273r10
    · first | exact hE_x273r11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273r11)
    · exact hB_x273r11
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x273r13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273r13)
    · exact hB_x273r13
    · first | exact hE_x273r15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x273r15)
    · exact hB_x273r15
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273mb0
    · exact hB_x273mb0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273mb8
    · exact hB_x273mb8
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273m100
    · exact hB_x273m100
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273m208
    · exact hB_x273m208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273m210
    · exact hB_x273m210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273m218
    · exact hB_x273m218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x273m220
    · exact hB_x273m220
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold RecRegs
    and_intros
    · simp [setRegF, hr4]
    · simp [setRegF, hr5]
    · simp [setRegF, hr14]
    · simp [hx]
  · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.RecipSeg
