import Fv256.Proofs.Arm64.R4Live
import Fv256.Proofs.Common.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec

namespace Fv256.Arm64.R4Seg

/-- `R4Post` with the stored value left open -/
def R4PostV (s s' : State) (v : Nat) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.sp - 8#64 ∧ s'.regs 30 = s.regs 30 ∧
  s'.mem.readLE (s.regs 0).toNat 32 = v ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem r4_exit (s S : State) (hpc : S.pc = BitVec.ofNat 64 (r4Entry + 0x314)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (l3 l4 l6 l7 : Nat) (hL : L314 S l3 l4 l6 l7) :
    ReachesRet Fv256.Arm64.ReduceProg.program (s.regs 30) S
      (fun S' => R4PostV s S' (l7 + 2 ^ 64 * l3 + 2 ^ 128 * l4 + 2 ^ 192 * l6)) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hbz, hbx, hbm, hbu, hm3, hmu⟩ := hs
  have hS := hR.sp_toNat hsb
  have hacc : S.mem.accessible (S.sp.toNat - 8) 184 true = true := by
    rw [hM.2.2.accessible]; rw [show S.sp.toNat - 8 = s.sp.toNat - 168 by omega]; exact hsd
  obtain ⟨hE3, hE4, hE6, hE7⟩ := hL
  have hz0 : S.mem.readLE (S.sp.toNat + 168) 8 = (s.regs 0).toNat := by
    rw [show S.sp.toNat + 168 = s.sp.toNat + 8 by omega]; exact hM.1
  have haz : S.mem.accessible (s.regs 0).toNat 32 true = true := by rw [hM.2.2.accessible]; exact hbz.2.1
  have hzb := hbz.1
  have hR30 : S.regs 30 = s.regs 30 := hR.2.2.2.1
  janus_run [hE3, hE4, hE6, hE7, hz0]
  have b3 : l3 < 2 ^ 64 := by rw [← hE3]; exact BitVec.isLt _
  have b4 : l4 < 2 ^ 64 := by rw [← hE4]; exact BitVec.isLt _
  have b6 : l6 < 2 ^ 64 := by rw [← hE6]; exact BitVec.isLt _
  have b7 : l7 < 2 ^ 64 := by rw [← hE7]; exact BitVec.isLt _
  all_goals (
  unfold R4PostV
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR.1]; exact BitVec.sub_add_cancel _ _
  · simp [setReg]
  · simp [setReg]; exact hR.2.2.2.2
  · simp [setReg]; exact hR.2.2.1
  · simp [setReg]; rw [hR.1]; bv_omega
  · simp [setReg]; exact hR30
  · rw [Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Nat.mod_eq_of_lt b3, Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b6, Nat.mod_eq_of_lt b7]
  · refine MemFrame.trans hM.2.2 (?_ : MemFrame S.mem _ [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) ?_
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
    · intro a n hx
      simp only [Outside, and_true] at hx ⊢
      omega)

end Fv256.Arm64.R4Seg
