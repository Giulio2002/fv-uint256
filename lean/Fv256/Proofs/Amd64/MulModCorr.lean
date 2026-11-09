import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.MulModProg
import Fv256.Proofs.Amd64.ReduceSpec
import Fv256.Proofs.Amd64.MulModEns
import Fv256.Proofs.Amd64.MulModSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModCorr

set_option maxRecDepth 100000 in
theorem hcSelf : Janus.Contracts.EqHashModel.CodeIn64 Fv256.MulModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem entry_eq : Fv256.Amd64.MulModSum.mulmodEntry = Extracted.entry := by decide

theorem correctness_param (hR4 : Fv256.Amd64.ReduceSpec.R4Summary) (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => StackGuardOK s 0x2f0 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x28 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x378) 0x3a0)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x28)]) :=
  Fv256.Amd64.MulModEns.ensures_mm
    (entry_eq ▸ Fv256.CodeIn.lib_summary hcSelf (Fv256.Amd64.MulModSum.mulmod_summary hR4)) z x y m

end Fv256.Amd64.MulModCorr
