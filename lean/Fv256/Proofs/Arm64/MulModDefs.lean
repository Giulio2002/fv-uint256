import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.RecipSpecA
import Fv256.Proofs.Arm64.ReduceSpec

/-!
# arm64 `MulMod` / `MulModWithReciprocal` glue: shared statements (Extracted-free)

`RecipSummaryU` is FV-B5's `RecipSummary` with `RecPre`/`RecSpec` unfolded (so that `janus_run` sees the facts of a call's post).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulModDefs

def RecipSummaryU : Prop :=
  Summary Fv256.Arm64.RecipProg.program Fv256.Arm64.RecipSeg.recEntry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
      (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 false = true ∧
      ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 0).toNat))
    (fun s s' => s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
      MemFrame s.mem s'.mem [(s.sp.toNat - 280, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] ∧
      (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192 → s'.mem.readLE (s.sp.toNat + 8) 40 = 0) ∧
      (2 ^ 192 ≤ s.mem.readLE (s.regs 0).toNat 32 →
        Fv256.F.RecipWeak (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
      (2 ^ 193 ≤ s.mem.readLE (s.regs 0).toNat 32 →
        Fv256.F.RecipOK (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE (s.sp.toNat + 8) 40)))

theorem recipU_of (h : Fv256.Arm64.RecipSeg.RecipSummary) : RecipSummaryU := h

end Fv256.Arm64.MulModDefs
