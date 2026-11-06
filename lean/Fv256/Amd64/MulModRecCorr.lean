import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.MulModRecProg
import Fv256.Amd64.ReduceSpec
import Fv256.Amd64.MulModRecEns
import Fv256.Amd64.MulModRecSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModRecCorr

set_option maxRecDepth 100000 in
theorem hcSelf : Janus.Contracts.EqHashModel.CodeIn64 Fv256.MulModRecProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem entry_eq : Fv256.Amd64.MulModRecSum.mulmodrecEntry = Extracted.entry := by decide

theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) (z x y m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m, mu]
      (fun s => StackGuardOK s 0x298 ∧ 0x2f0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x2e8 0x30 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
        Fv256.F.MuOK (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x2e8) 0x318)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x2e8, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x30)]) :=
  Fv256.Amd64.MulModRecEns.ensures_mr
    (entry_eq ▸ Fv256.CodeIn.lib_summary hcSelf (Fv256.Amd64.MulModRecSum.mulmodrec_summary hR4)) z x y m mu

end Fv256.Amd64.MulModRecCorr
