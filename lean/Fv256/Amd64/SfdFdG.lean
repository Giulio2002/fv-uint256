import Fv256.Amd64.SfdFdF

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

/-- the loop from the head, by induction on the rounds left -/
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
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS.toNat ≠ 0) :
    ∀ (k i : Nat) (S : State), 5 - i = k → FdInv R R2 T b L lo hi z pS nS s i S →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S (FdPost R R2 T b L lo hi z pS nS s) := by
  intro k
  induction k with
  | zero =>
    intro i S hk hI
    exact fd_nil impl R R2 T b L lo hi z pS nS s hpre hn S i hI (Or.inl (by have := hI.2.1; omega))
  | succ k ih =>
    intro i S hk hI
    by_cases hex : nS.toNat ≤ 19 * i
    · exact fd_nil impl R R2 T b L lo hi z pS nS s hpre hn S i hI (Or.inr hex)
    · exact fd_round impl R R2 T b L lo hi z pS nS s hif hnew hmg hmv hwb1 hwb2 hpre S i hI (by omega) (by omega)
        (fun S' hI' => ih (i + 1) S' (by omega) hI')

set_option maxHeartbeats 16000000 in
theorem fd_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
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
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (Extracted.program.link impl) fd (FdPre R R2 T b L lo hi z pS nS) (FdPost R R2 T b L lo hi z pS nS) := by
  intro s hpc hpre
  by_cases hn : nS = 0
  · exact fd_eof impl R R2 T b L lo hi z pS nS s hpc hpre hn
  · have hn' : nS.toNat ≠ 0 := fun h => hn (BitVec.eq_of_toNat_eq h)
    refine Fv256.SegCompose.seg_trans (fd_pro impl R R2 T b L lo hi z pS nS s hpc hpre hn) ?_
    intro S hpc1 hI
    exact fd_loop impl R R2 T b L lo hi z pS nS s hif hnew hmg hmv hwb1 hwb2 hpre hn' 5 0 S rfl hI

end Fv256.Amd64.SfdFd
