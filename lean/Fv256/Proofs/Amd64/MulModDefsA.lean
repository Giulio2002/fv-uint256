import Fv256.Proofs.Amd64.RecipSummary

/-!
# amd64 `MulMod` glue: `Reciprocal`'s summary with `RecPre`/`RecSpec` unfolded (so that `janus64_run` sees the facts of the post)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModDefsA

def RecipSummaryU : Prop :=
  Summary Fv256.RecipProg.program Fv256.Amd64.RecipSeg.recEntry
    (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
      0x248 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x1b8 ∧ StackWritable s 0x240 0x30 ∧ s.xmm 15 = 0 ∧
      Buffer s (s.regs 0) 32 false ∧
      Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x240) 0x270 ∧
      Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x240) 0x270)
    (fun s s' =>
      s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
      MemFrame s.mem s'.mem [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)] ∧
      (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192 → s'.mem.readLE ((s.regs 4).toNat + 8) 40 = 0) ∧
      (2 ^ 192 ≤ s.mem.readLE (s.regs 0).toNat 32 →
        Fv256.F.RecipWeak (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE ((s.regs 4).toNat + 8) 40)) ∧
      (2 ^ 193 ≤ s.mem.readLE (s.regs 0).toNat 32 →
        Fv256.F.RecipOK (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE ((s.regs 4).toNat + 8) 40)))

theorem recipU : RecipSummaryU := Fv256.Amd64.RecipSeg.recip_summary

end Fv256.Amd64.MulModDefsA
