import Extracted
import Fv256.Amd64.DecExt
import Fv256.Amd64.DecLiftGen

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

theorem dec_summary_ext_gen (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (G : Nat → Nat → Memory → Prop) (hG : ∀ r0 r1 m m', rtView rt m = rtView rt m' → G r0 r1 m → G r0 r1 m')
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (Fv256.Arm64.SbtsG.sbtsG Extracted.dataAddr.«runtime.staticuint64s» G)) :
    Summary (Extracted.program.link impl) decE
      (fun s => s.regs 0 = z ∧ StackGuardOK s 4568 ∧ StackWritable s 4568 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4568) (4568 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 384 - 0x58) (rtView rt s.mem)) ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 140737488355328)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) ∧
        Fv256.E.DecAt rt 5163273 5176582 5134938 (s'.regs 0).toNat (s'.regs 3).toNat ∧
        (valueAt s z 32 < 100 → MemFrame s.mem s'.mem [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) ∧
        (100 ≤ valueAt s z 32 → G (s'.regs 0).toNat (s'.regs 3).toNat s'.mem)) :=
  dec_summary_E_gen Extracted.dataAddr.«runtime.staticuint64s» hLib (by decide) impl rt H z G hG hc

end Fv256.Amd64.Dec
