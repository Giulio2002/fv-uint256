import Extracted
import Fv256.Arm64.DecLift

/-! `dec_summary` over the consumer's `Extracted.program` (the only `Extracted`-dependent part of the decimal proofs). -/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem hLib : Fv256.Arm64.LinkEq.LibIn Fv256.Arm64.DecProg.program Extracted.program :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem dec_summary_ext (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Summary (Extracted.program.link impl) decE
      (fun s => s.regs 0 = z ∧ GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem)) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)])) :=
  dec_summary_E Extracted.dataAddr.«runtime.staticuint64s» hLib (by decide) impl rt H z hc

end Fv256.Arm64.Dec
