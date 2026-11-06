import Fv256.Amd64.SfdFdRnd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

abbrev mid : Nat := fd + 0x117

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- from the return of `ParseUint` (either call site) with `err = nil` to the merge point `mid` -/
theorem fd_ret_to_mid (impl : List Janus.Amd64.Segment) (S' : State) (RA : Nat) (hRA : RA = 4933783 ∨ RA = 4933806)
    (hpc : S'.rip = BitVec.ofNat 64 RA) (h3 : S'.regs 3 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 mid) S'
      (fun S2 => S2.rip = BitVec.ofNat 64 mid ∧ S2.mem = S'.mem ∧ S2.regs 0 = S'.regs 0 ∧ S2.regs 1 = S'.regs 1 ∧
        S2.regs 3 = S'.regs 3 ∧ S2.regs 4 = S'.regs 4 ∧ S2.regs 5 = S'.regs 5 ∧ S2.regs 14 = S'.regs 14 ∧
        S2.xmm 15 = S'.xmm 15 ∧ S2.df = S'.df ∧ S2.fsBase = S'.fsBase) := by
  have hz : S'.regs 3 = 0 := h3
  rcases hRA with rfl | rfl
  all_goals
    janus64_run [hz] until [mid]
    all_goals trace_state
    all_goals sorry

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the error return of `fromDecimal` (`TESTQ BX,BX; JNE` taken): `(AX, BX) := (BX, CX)`, epilogue, `RET` -/
theorem fd_err_ret (impl : List Janus.Amd64.Segment) (S' : State) (RA : Nat) (hRA : RA = 4933783 ∨ RA = 4933806)
    (ra bp : BitVec 64) (hpc : S'.rip = BitVec.ofNat 64 RA) (h3 : S'.regs 3 ≠ 0)
    (hbp : S'.mem.readLE ((S'.regs 4).toNat + 136) 8 = bp.toNat) (hret : S'.mem.readLE ((S'.regs 4).toNat + 144) 8 = ra.toNat)
    (hacc : S'.mem.accessible ((S'.regs 4).toNat + 136) 16 false = true) (hsp64 : (S'.regs 4).toNat + 152 < 2 ^ 64) :
    ReachesRet (Extracted.program.link impl) ra S'
      (fun S'' => S''.regs 0 = S'.regs 3 ∧ S''.regs 3 = S'.regs 1 ∧ S''.regs 4 = S'.regs 4 + 152#64 ∧ S''.regs 5 = bp ∧
        S''.regs 14 = S'.regs 14 ∧ S''.xmm 15 = S'.xmm 15 ∧ S''.df = S'.df ∧ S''.fsBase = S'.fsBase ∧ S''.mem = S'.mem) := by
  have hz : S'.regs 3 ≠ 0 := h3
  rcases hRA with rfl | rfl
  all_goals
    janus64_run [hz, hbp, hret, hacc, hsp64]
    all_goals trace_state
    all_goals sorry

end Fv256.Amd64.SfdFd
