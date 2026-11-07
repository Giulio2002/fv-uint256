import Extracted
import Fv256.Arm64.UnmarshalTextHead

/-! audit probe: the statements of `UnmarshalTextMain.correctness` / `Witness.nonvacuous` with sorry bodies -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalHex Fv256.Arm64.UnmarshalPost Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalTextAudit

theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16)
    (hsb : RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalText.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalText.stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => PreU Fv256.Arm64.UnmarshalText.cfg Fv256.Arm64.UnmarshalText.sbAddr Fv256.Arm64.UnmarshalText.stAddr R R2 T b L lo hi
          z pI nI s ∧ HexEnv R lo hi z s)
      (fun s s' => UTPost Fv256.Arm64.UnmarshalText.cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  sorry

namespace Witness

theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalText.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalText.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    PreU Fv256.Arm64.UnmarshalText.cfg Fv256.Arm64.UnmarshalText.sbAddr Fv256.Arm64.UnmarshalText.stAddr R R2 T b L lo hi z pI nI s ∧
    HexEnv R lo hi z s := by
  sorry

end Witness

end Fv256.Arm64.UnmarshalTextAudit
