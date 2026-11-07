import Extracted
import Fv256.Amd64.MustFromDecimal
import Fv256.Amd64.MustFromDecimalHsfd

import Fv256.Amd64.AMFdWitC

/-!
# `MustFromDecimal` (amd64): the Extracted-level theorem (`hhex`/`hsfd` discharged) and its non-vacuity witnesses
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Janus.Contracts.PanicAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

open Fv256.Amd64.MustFromDecimal

namespace Fv256.Amd64.MustFromDecimalMain

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
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
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]))
      (fun s v _ =>
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
        (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
          InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)) := by
  exact Fv256.Amd64.MustFromDecimal.correctness_cond P impl R R2 T b L lo hi pS nS hif hnew hmg hmv hwb1 hwb2 (Fv256.Amd64.MustFromDecimalHsfd.hsfd impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp)

namespace Witness

set_option maxRecDepth 100000 in
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (pS nS : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pS, nS] s ∧
    (Fv256.Amd64.MFdWit.pinPanicRuntime P ∧ Fv256.Amd64.MustFromDecimal.Pre R R2 T b L lo hi pS nS s) := Fv256.Amd64.MFdWit.nonvacuous_core

end Witness

end Fv256.Amd64.MustFromDecimalMain
