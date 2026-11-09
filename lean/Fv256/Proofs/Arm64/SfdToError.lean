import Fv256.Proofs.Arm64.SfdTeSum0
import Fv256.Proofs.Arm64.SfdTeSum1

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

theorem summary_split {p : Program} {e : Nat} {P : State → Prop} {c : State → Prop} {Q : State → State → Prop}
    (h0 : Summary p e (fun s => P s ∧ c s) Q) (h1 : Summary p e (fun s => P s ∧ ¬ c s) Q) : Summary p e P Q := by
  intro s hpc hP
  by_cases hc : c s
  · exact h0 s hpc ⟨hP, hc⟩
  · exact h1 s hpc ⟨hP, hc⟩

theorem te_sum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (P.link impl) te (TePre R R2 T b L fp fl sp sl) (TePost R R2 b L fp fl sp sl) :=
  summary_split (c := fun s => s.mem.readLE wbFlag 4 = 0)
    (te_sum0 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)
    (te_sum1 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)

end Fv256.Arm64.SfdToError
