import Fv256.Arm64.R4Live

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.ReduceSpec

namespace Fv256.Arm64.R4Seg

/-- `R4Post` with the stored value left open -/
def R4PostV (s s' : State) (v : Nat) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.sp - 8#64 ∧ s'.regs 30 = s.regs 30 ∧
  s'.mem.readLE (s.regs 0).toNat 32 = v ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat), (s.sp.toNat + 8, s.sp.toNat + 16)]

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
  have hz : S.regs 30 = s.regs 30 := hR.2.2.2.1
  janus_run [hE3, hE4, hE6, hE7, hM.1]
  all_goals (trace_state; sorry)

end Fv256.Arm64.R4Seg
