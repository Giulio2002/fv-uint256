import Extracted
import Fv256.Proofs.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.UnmarshalJSON
import Fv256.Proofs.Amd64.UnmarshalJSONHsfd
import Fv256.Proofs.Amd64.UnmarshalHexDisch
import Fv256.Proofs.Amd64.AUjWitC

/-!
# `UnmarshalJSON` (amd64): the Extracted-level theorem (`hhex`/`hsfd` discharged) and its non-vacuity witnesses
-/

open Fv256.Amd64.UnmarshalQ
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDecJ Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

open Fv256.Amd64.UnmarshalJSON

namespace Fv256.Amd64.UnmarshalJSONMain

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
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
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)

    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16)
    : Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => ((PreU0m cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ (¬ Quoted s.mem pI.toNat nI.toNat → OkOut sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧ (Quoted s.mem pI.toNat nI.toNat → QPre cfg sbAddr R b lo pI nI s))
      (fun s s' =>
        (Quoted s.mem pI.toNat nI.toNat →
          (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
          (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab))) ∧
        (¬ Quoted s.mem pI.toNat nI.toNat →
          (∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])) := by
  exact Fv256.Amd64.UnmarshalJSON.correctness_cond impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb (Fv256.Amd64.UnmarshalHexDisch.hhex_of impl) (Fv256.Amd64.UnmarshalJSONHsfd.hsfd impl R R2 T hif hnew hmg hmv hwb1 hwb2 hcmp)

namespace Witness

set_option maxRecDepth 100000 in
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract64 (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    (((PreU0m Fv256.Amd64.UnmarshalJSON.cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
        (¬ Quoted s.mem pI.toNat nI.toNat → OkOut Fv256.Amd64.UnmarshalTextS.sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧
      (Quoted s.mem pI.toNat nI.toNat → QPre Fv256.Amd64.UnmarshalJSON.cfg Fv256.Amd64.UnmarshalTextS.sbAddr R b lo pI nI s)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (Quoted s.mem pI.toNat nI.toNat →
          (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
          (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab))) ∧
        (¬ Quoted s.mem pI.toNat nI.toNat →
          (∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, cs1, cs2, cs3, cs4, cs5, cs6, cs7, cs8, hret, hsetup, hp9⟩ := Fv256.Amd64.UjWit.nonvacuous_core
  exact ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, cs1, cs2, cs3, cs4, cs5, cs6, cs7, cs8, hret, hsetup, hp9,
    correctness impl R R2 T b L lo hi z pI nI cI h1 h2 h3 h4 h5 h6 h8 h7 ret hret s hsetup hp9⟩

set_option maxRecDepth 100000 in
theorem unquoted : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract64 (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    (((PreU0m Fv256.Amd64.UnmarshalJSON.cfg Fv256.Amd64.UnmarshalTextS.sbAddr Fv256.Amd64.UnmarshalTextS.stAddr R R2 T b L lo hi z pI nI s ∧
        (¬ Quoted s.mem pI.toNat nI.toNat → OkOut Fv256.Amd64.UnmarshalTextS.sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧
      (Quoted s.mem pI.toNat nI.toNat → QPre Fv256.Amd64.UnmarshalJSON.cfg Fv256.Amd64.UnmarshalTextS.sbAddr R b lo pI nI s)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (Quoted s.mem pI.toNat nI.toNat →
          (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
          (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab))) ∧
        (¬ Quoted s.mem pI.toNat nI.toNat →
          (∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, cs1, cs2, cs3, cs4, cs5, cs6, cs7, cs8, hret, hsetup, hp9⟩ := Fv256.Amd64.UjWit.unq_core
  exact ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, h1, h2, h3, h4, h5, h6, h7, h8, cs1, cs2, cs3, cs4, cs5, cs6, cs7, cs8, hret, hsetup, hp9,
    correctness impl R R2 T b L lo hi z pI nI cI h1 h2 h3 h4 h5 h6 h8 h7 ret hret s hsetup hp9⟩

end Witness

end Fv256.Amd64.UnmarshalJSONMain
