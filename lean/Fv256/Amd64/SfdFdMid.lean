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
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (BitVec.ofNat 64 mid) S'
      (fun S2 => S2.rip = BitVec.ofNat 64 mid ∧ S2.mem = S'.mem ∧ S2.regs 0 = S'.regs 0 ∧ S2.regs 1 = S'.regs 1 ∧
        S2.regs 3 = S'.regs 3 ∧ S2.regs 4 = S'.regs 4 ∧ S2.regs 5 = S'.regs 5 ∧ S2.regs 14 = S'.regs 14 ∧
        S2.xmm 15 = S'.xmm 15 ∧ S2.df = S'.df ∧ S2.fsBase = S'.fsBase) := by
  have hz : S'.regs 3 = 0 := h3
  rcases hRA with rfl | rfl
  all_goals
    janus64_run [hz] until [mid]
    all_goals (
      refine reach_name ?_
      intro S2 hS2
      refine ReachesRet.done (by rw [hS2]; first | rfl | decide | simp [mid, fd]) ?_
      subst hS2
      exact ⟨by first | rfl | decide | simp [mid, fd], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the error return of `fromDecimal` (`TESTQ BX,BX; JNE` taken): `(AX, BX) := (BX, CX)`, epilogue, `RET` -/
theorem fd_err_ret (impl : List Janus.Amd64.Segment) (S' : State) (RA : Nat) (hRA : RA = 4933783 ∨ RA = 4933806)
    (ra bp : BitVec 64) (hra : ra.toNat < 2 ^ 47) (hpc : S'.rip = BitVec.ofNat 64 RA) (h3 : S'.regs 3 ≠ 0)
    (hbp : S'.mem.readLE ((S'.regs 4).toNat + 136) 8 = bp.toNat) (hret : S'.mem.readLE ((S'.regs 4).toNat + 144) 8 = ra.toNat)
    (hacc : S'.mem.accessible ((S'.regs 4).toNat + 136) 16 false = true) (hsp64 : (S'.regs 4).toNat + 152 < 2 ^ 64) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) ra S'
      (fun S'' => S''.regs 0 = S'.regs 3 ∧ S''.regs 3 = S'.regs 1 ∧ S''.regs 4 = S'.regs 4 + 152#64 ∧ S''.regs 5 = bp ∧
        S''.regs 14 = S'.regs 14 ∧ S''.xmm 15 = S'.xmm 15 ∧ S''.df = S'.df ∧ S''.fsBase = S'.fsBase ∧ S''.mem = S'.mem) := by
  have hz : ¬ (S'.regs 3).toNat = 0 := fun h => h3 (BitVec.eq_of_toNat_eq h)
  rcases hRA with rfl | rfl
  all_goals
    janus64_run [hz, hbp, hret, hacc, hsp64, hra]

/-- the merge point after `ParseUint` returned the digits value `d` of round `i` (no error) -/
def MidInv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i d : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 mid ∧ i < 5 ∧ 19 * i < nS.toNat ∧ d < 2 ^ 64 ∧
  S.regs 0 = BitVec.ofNat 64 d ∧ S.regs 3 = 0 ∧ S.regs 1 = 0 ∧
  S.regs 4 = s0.regs 4 - 144#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
  S.fsBase = s0.fsBase ∧
  S.mem.readLE ((s0.regs 4).toNat - 104) 8 = i ∧ S.mem.readLE ((s0.regs 4).toNat - 96) 8 = nS.toNat - 19 * i ∧
  S.mem.readLE ((s0.regs 4).toNat - 112) 8 = nS.toNat - 19 * i ∧
  S.mem.readLE ((s0.regs 4).toNat - 56) 8 = s0.mem.readLE (mulTab + 8 * i) 8 ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.regs 4).toNat 8 = s0.mem.readLE (s0.regs 4).toNat 8 ∧
  S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s0.regs 4).toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE ((s0.regs 4).toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat i ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - i) i ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i) ∧
  d = decSum (Fv256.C.bytesAt s0.mem pS.toNat) (chunkBounds nS.toNat 0 i).1 (nS.toNat - 19 * i - (chunkBounds nS.toNat 0 i).1) ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * i) nS.toNat

theorem TeObj.congr_mem {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s s' s'' : State} {q t : Nat}
    (h : TeObj R b L fp fl sp sl s s' q t) (hm : s''.mem = s'.mem) : TeObj R b L fp fl sp sl s s'' q t := by
  unfold TeObj at *
  rw [hm]; exact h

end Fv256.Amd64.SfdFd
