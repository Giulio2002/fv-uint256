import Extracted
import Fv256.Amd64.UnmarshalTextS0
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.UnmarshalSpec
import Fv256.DecCongr
import Fv256.Amd64.UnmarshalDec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.FromHexLib
import Fv256.Amd64.UnmarshalTextSa
import Fv256.Amd64.UnmarshalTextSx
import Fv256.Amd64.UnmarshalTextSX
import Fv256.Amd64.UnmarshalTextSb
import Fv256.Amd64.UnmarshalTextSc

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalTextS

open Fv256.Amd64.UnmarshalTextS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem ut_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) 4922368 (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Summary (Extracted.program.link impl) utEntry
      (fun s => PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' =>
        (IsHex s.mem pI.toNat nI.toNat →
          (∀ v, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (∀ e, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .error e →
            s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
            s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
        (¬ IsHex s.mem pI.toNat nI.toNat →
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
  intro s hpc hpre
  obtain ⟨hpreU, henv, hdl⟩ := hpre
  by_cases h1 : (nI.toNat : Int) < 2
  · exact br_a impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hhex hsfd s hpc ⟨⟨hpreU, henv, hdl⟩, h1⟩
  by_cases h2 : s.mem.readLE pI.toNat 1 = 48
  · by_cases h3 : Bw s.mem pI.toNat - 120#8 = 0#8
    · exact br_x impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hhex hsfd s hpc ⟨⟨hpreU, henv, hdl⟩, h1, h2, h3⟩
    · by_cases h4 : Bw s.mem pI.toNat - 88#8 = 0#8
      · exact br_X impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hhex hsfd s hpc ⟨⟨hpreU, henv, hdl⟩, h1, h2, h3, h4⟩
      · exact br_b impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hhex hsfd s hpc ⟨⟨hpreU, henv, hdl⟩, h1, h2, h3, h4⟩
  · exact br_c impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hhex hsfd s hpc ⟨⟨hpreU, henv, hdl⟩, h1, h2⟩

end Fv256.Amd64.UnmarshalTextS
