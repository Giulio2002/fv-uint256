import Fv256.Arm64.R4Live

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec

namespace Fv256.Arm64.R4Seg

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem r4_pro (s : State) (hpc : s.pc = BitVec.ofNat 64 r4Entry) (hs : R4Pre s) 
    :
    ReachesRet Fv256.Arm64.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x20)) s (fun S' =>
      L20 S' (s.regs 1).toNat (s.regs 2).toNat (s.regs 3).toNat ∧ R4Regs s S' ∧ R4Mem s S'.mem) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hbz, hbx, hbm, hbu, hm3, hmu⟩ := hs
  janus_run [] until [r4Entry + 0x20]
  all_goals (
  refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [r4Entry, segAddr]) ?_
  refine ⟨?_, ?_, ?_⟩
  · unfold L20
    and_intros <;> simp [setReg]
  · unfold R4Regs
    and_intros
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
  · unfold R4Mem
    and_intros
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 168, s.sp.toNat + 16)) (by simp) (by dsimp only; omega) (by dsimp only; omega))

end Fv256.Arm64.R4Seg
