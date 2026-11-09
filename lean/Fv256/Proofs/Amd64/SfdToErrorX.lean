import Fv256.Proofs.Amd64.SfdProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Amd64.SfdEnv
import Fv256.Proofs.Amd64.SfdTePre
import Fv256.Proofs.Amd64.SfdTeLem
import Fv256.Proofs.Amd64.SfdTeSum0
import Fv256.Proofs.Amd64.SfdTeSum1

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.Amd64.SfdEnv

namespace Fv256.Amd64.SfdToError

theorem summary_split {p : Janus.Amd64.Program} {e : Nat} {P : State → Prop} {c : State → Prop} {Q : State → State → Prop}
    (h0 : Summary p e (fun s => P s ∧ c s) Q) (h1 : Summary p e (fun s => P s ∧ ¬ c s) Q) : Summary p e P Q := by
  intro s hpc hP
  by_cases hc : c s
  · exact h0 s hpc ⟨hP, hc⟩
  · exact h1 s hpc ⟨hP, hc⟩

theorem te_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Ifaceeq (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Fv256.Amd64.SfdProg.program.link impl)
      (Fv256.Amd64.SfdProg.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (Fv256.Amd64.SfdProg.program.link impl) te (TePre R R2 T b L fp fl sp sl) (TePost R R2 b L fp fl sp sl) := by
  exact summary_split (c := fun s => s.mem.readLE 6156064 4 = 0)
    (te_sum0 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)
    (te_sum1 impl R R2 hl T b L fp fl sp sl hif hnew hmg hmv hwb1 hwb2)
end Fv256.Amd64.SfdToError
