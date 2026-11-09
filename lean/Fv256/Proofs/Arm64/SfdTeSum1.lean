import Fv256.Proofs.Arm64.SfdTe1Pre
import Fv256.Proofs.Arm64.SfdTe1Tail

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

theorem te_sum1 (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (P.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ s.mem.readLE wbFlag 4 ≠ 0)
      (TePost R R2 b L fp fl sp sl) :=
  te1_pre impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2
    (fun s S St m' m2 m3 m4 q t => te_tail1 impl R R2 b L fp fl sp sl s S St m' m2 m3 m4 q t hwb1 hwb2)

end Fv256.Arm64.SfdToError
