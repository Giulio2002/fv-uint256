import Extracted
import Fv256.Proofs.Arm64.DecExt
import Fv256.Proofs.Arm64.DecLiftGen

/-! `dec_summary_gen` over the consumer's `Extracted.program`: the strengthened `Dec` summary whose postcondition also carries a ghost
fact `G` about the string `slicebytetostring` returned and the memory (the live-runtime state after the call), for a contract whose spec
is `sbtsG`. -/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

theorem dec_summary_ext_gen (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (G : Nat → Nat → Memory → Prop) (hG : ∀ r0 r1 m m', rtView rt m = rtView rt m' → G r0 r1 m → G r0 r1 m')
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H
      (Fv256.Arm64.SbtsG.sbtsG Extracted.dataAddr.«runtime.staticuint64s» G)) :
    Summary (Extracted.program.link impl) decE
      (fun s => s.regs 0 = z ∧ GuardOK s 4576 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
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
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) ∧
        Fv256.E.DecAt rt 989280 1002589 960826 (s'.regs 0).toNat (s'.regs 1).toNat ∧
        (val256 s.mem z.toNat < 100 → MemFrame s.mem s'.mem [(s.sp.toNat - 4608, s.sp.toNat - 8)]) ∧
        (100 ≤ val256 s.mem z.toNat → G (s'.regs 0).toNat (s'.regs 1).toNat s'.mem)) :=
  dec_summary_E_gen Extracted.dataAddr.«runtime.staticuint64s» hLib (by decide) impl rt H z G hG hc

end Fv256.Arm64.Dec
