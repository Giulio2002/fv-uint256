import Extracted
import Fv256.SfdFdMath
import Fv256.SfdFdLem
import Fv256.Amd64.SfdFd
import Fv256.Amd64.SfdMul
import Fv256.UtilB2

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

abbrev head : Nat := fd + 0xa0

/-- the state at the loop head after `i` rounds -/
def FdInv (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s0 : State) (i : Nat) (S : State) : Prop :=
  S.rip = BitVec.ofNat 64 head ∧ i ≤ 5 ∧
  S.regs 0 = z ∧ S.regs 3 = pS ∧ S.regs 2 = BitVec.ofNat 64 i ∧ S.regs 1 = nS - BitVec.ofNat 64 (19 * i) ∧
  (19 * i < nS.toNat → S.regs 6 = nS - BitVec.ofNat 64 (19 * i)) ∧
  S.regs 4 = s0.regs 4 - 144#64 ∧ S.regs 5 = s0.regs 4 - 8#64 ∧ S.regs 14 = s0.regs 14 ∧ S.xmm 15 = 0 ∧ S.df = false ∧
  S.fsBase = s0.fsBase ∧
  MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  S.mem.readLE (s0.regs 4).toNat 8 = s0.mem.readLE (s0.regs 4).toNat 8 ∧
  S.mem.readLE ((s0.regs 4).toNat - 8) 8 = (s0.regs 5).toNat ∧
  S.mem.readLE ((s0.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s0.regs 4).toNat + 16) 8 = pS.toNat ∧
  (∀ k, k < 5 → S.mem.readLE ((s0.regs 4).toNat - 48 + 8 * k) 8 = s0.mem.readLE (mulTab + 8 * k) 8) ∧
  Janus.Spec.val256 S.mem z.toNat = accV (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat i ∧
  Env R R2 T b L lo hi S ∧
  firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 5 0 = firstBad (Fv256.C.bytesAt s0.mem pS.toNat) nS.toNat 0 (5 - i) i ∧
  allDec (Fv256.C.bytesAt s0.mem pS.toNat) (nS.toNat - 19 * i) nS.toNat

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem fd_loop (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State)
    (hif : Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) :
    ∀ n (S : State) (i : Nat), n = 5 - i → FdInv R R2 T b L lo hi z pS nS s i S →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i hn hI
    obtain ⟨hpc, hi5, r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs, hfr, mret, mbp, mz, mp, mtab, mval, hEnvS, hfb, hall⟩ := hI
    by_cases hi5' : i = 5
    · sorry
    · by_cases hrem : 19 * i < nS.toNat
      · janus64_run [r0, r3, r2, r1, r6, r4, r5, r14, rx15, rdf, rfs] until [head] calls [pw_sum impl R R2 T b L lo hi _ _ hif hnew hmg hmv hwb1 hwb2, Fv256.B.summary_link impl (Fv256.Amd64.SfdMul.mul_sum _ _ _)]
        trace_state
        sorry
      · sorry

end Fv256.Amd64.SfdFd
