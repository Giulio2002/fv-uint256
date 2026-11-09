import Extracted
import Fv256.Spec.Amd64.FormatTransfer

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

namespace Fv256.Amd64.FormatWitA

/-- type pins for the witnesses' existential variables (the printed statement has no binder types) -/
def pinT (_z _tab _data _ch : BitVec 64) (_ret : Nat) (_s : State) (_rt : List (Nat × Nat)) (_impl : List Amd64.Segment) (_R : Janus.Spec.Type.IfaceModel)
    (_H : Janus.Contracts.RtReady) (_R2 : Janus.Contracts.RtInv) (_RW _RP _RF _RWr _RFp _RBf : Janus.Contracts.ICall.Res) : Prop := True

section Rest

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

end Rest

section TA

open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceAmd64 Janus.Spec.Type

open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

end TA

end Fv256.Amd64.FormatWitA
