import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdFdSpec

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I

namespace Fv256.Arm64.SfdTop

abbrev sfd : Nat := segAddr Fv256.Arm64.SfdProg.program "github.com/holiman/uint256.(*Int).SetFromDecimal"
/-- after the stack check, the frame, the spills and the `+` skip -/
abbrev ta : Nat := sfd + 0x40

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem top_pro_probe (impl : List Segment) (s : State) (z pS nS : BitVec 64) (lo hi : Nat)
    (hpc : s.pc = BitVec.ofNat 64 0xb89b0) (h0 : s.regs 0 = z) (h1 : s.regs 1 = pS) (h2 : s.regs 2 = nS)
    (hlo : lo + 4528 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi) (hhi2 : hi ≤ 2 ^ 48)
    (hg : s.mem.readLE ((s.regs 28).toNat + 16) 8 < lo) (hga : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hacc : s.mem.accessible (s.sp.toNat - 88) 120 true = true)
    (hpA : s.mem.accessible pS.toNat nS.toNat false = true) (hpB : pS.toNat + nS.toNat ≤ 2 ^ 48)
    (hal : s.sp.toNat % 16 = 0) (hg48 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) :
    ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (BitVec.ofNat 64 0xb89f0) s (fun S => True) := by
  by_cases hn : nS = 0
  · subst hn
    janus_run [hpc, h0, h1, h2, hacc, hg, hga, hal, Nat.mod_eq_of_lt (show (s.regs 28).toNat + 16 < 2 ^ 64 by omega)] until [0xb89f0]
    all_goals trace_state
    all_goals sorry
  · all_goals sorry

end Fv256.Arm64.SfdTop
