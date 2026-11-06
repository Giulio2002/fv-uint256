import Fv256.Arm64.RecipProg
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Fv256.Arm64.RecipSeg
abbrev recEntry : Nat := segAddr Fv256.Arm64.RecipProg.program "github.com/holiman/uint256.Reciprocal"

def RecPre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
  (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 false = true ∧
  ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 0).toNat)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem seg0 (s : State) (hpc : s.pc = BitVec.ofNat 64 recEntry) (hpre : RecPre s) (Q : State → Prop)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hnp : ¬ (((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) &&& (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64)) ||| (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8) ||| (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8))))).toNat = 0)
    (hnp2 : ¬ ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) &&& (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64)) ||| (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8) ||| (BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8)))) = 0#64) :
    ReachesRet Fv256.Arm64.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x88)) s Q := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hpre
  janus_run until [recEntry + 0x88]
  all_goals (trace_state; sorry)
end Fv256.Arm64.RecipSeg
