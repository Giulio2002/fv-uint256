import Fv256.Arm64.SfdFdRnd

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw Fv256.Arm64.SfdFd

namespace Fv256.Arm64.SfdFd

abbrev mid : Nat := fd + 0x114

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- from the return of `ParseUint` (either call site) to the merge point `mid`: only `R4` is reloaded from the spill slot -/
theorem fd_ret_to_mid (impl : List Segment) (s' : State) (sp0 r : Nat) (RA : Nat) (hRA : RA = 756796 ∨ RA = 756828)
    (hpc : s'.pc = BitVec.ofNat 64 RA) (hsp : s'.sp.toNat = sp0 - 160)
    (hacc : s'.mem.accessible (s'.sp.toNat + 48) 8 false = true)
    (hr : s'.mem.readLE (s'.sp.toNat + 48) 8 = r) (hsp64 : s'.sp.toNat + 48 < 2 ^ 64) (hal : s'.sp.toNat % 16 = 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) (BitVec.ofNat 64 mid) s'
      (fun S2 => S2.pc = BitVec.ofNat 64 mid ∧ S2.mem = s'.mem ∧ S2.sp = s'.sp ∧ S2.regs 0 = s'.regs 0 ∧ S2.regs 1 = s'.regs 1 ∧
        S2.regs 4 = BitVec.ofNat 64 r ∧ S2.regs 28 = s'.regs 28 ∧ S2.regs 29 = s'.regs 29 ∧ S2.regs 18 = s'.regs 18 ∧
        S2.flags = (addSub (BitVec.ofNat 64 r) 19#64 true).snd) := by
  rcases hRA with rfl | rfl
  all_goals
    janus_run [hacc, hr, Nat.mod_eq_of_lt hsp64, hal] until [mid]
    refine Janus.Tactic.ReachesRet.done (by first | rfl | decide | simp [mid, fd]) ?_
    refine ⟨by first | rfl | simp [mid, fd], rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | simp [setReg_apply]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- the error return of `fromDecimal` (`CBNZ R1` taken): `(X0, X1) := (X1, X2)`, epilogue, `RET` -/
theorem fd_err_ret (impl : List Segment) (S2 : State) (x29 x30 : BitVec 64) (hpc : S2.pc = BitVec.ofNat 64 mid)
    (h1 : S2.regs 1 ≠ 0)
    (hx29 : S2.mem.readLE (S2.sp.toNat - 8) 8 = x29.toNat) (hx30 : S2.mem.readLE S2.sp.toNat 8 = x30.toNat)
    (hacc : S2.mem.accessible (S2.sp.toNat - 8) 16 false = true) (hsp64 : S2.sp.toNat + 160 < 2 ^ 64) (hsp8 : 8 ≤ S2.sp.toNat)
    (hal : S2.sp.toNat % 16 = 0) (h56 : x30.toNat < 2 ^ 56) (h4 : x30.toNat % 4 = 0) :
    ReachesRet ((Fv256.Arm64.SfdToError.P).link impl) x30 S2
      (fun S' => S'.sp = S2.sp + 160#64 ∧ S'.regs 0 = S2.regs 1 ∧ S'.regs 1 = S2.regs 2 ∧ S'.regs 29 = x29 ∧
        S'.regs 28 = S2.regs 28 ∧ S'.regs 18 = S2.regs 18 ∧ S'.mem = S2.mem) := by
  have hx29' : S2.mem.readLE (S2.sp.toNat - 8) 8 = x29.toNat := hx29
  janus_run [hacc, hx29, hx30, hsp64, hsp8, hal, h1, h56, h4]
  all_goals trace_state
  all_goals sorry

end Fv256.Arm64.SfdFd
