import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.ExpFinal
import Fv256.UtilF
import Fv256.Amd64.ExpSum
import Fv256.Amd64.ExpLoop1
import Fv256.Amd64.ExpLoop2
import Fv256.Amd64.ExpLoop3
import Fv256.Amd64.ExpLoop4
import Fv256.Amd64.EnsuresOfW

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ExpMain

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem exp_summary :
    Summary Extracted.program Extracted.entry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x100 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x20 ∧ StackWritable s 0xa8 0x20 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0xa8 ∨ (s.regs 4).toNat + 0x20 ≤ (s.regs 14).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0xa8, (s.regs 4).toNat + 0x20)]) := by
  sorry

theorem correctness (z b e : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b, e]
      (fun s => StackGuardOK s 0x20 ∧ 0x100 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xa8 0x20 ∧ Buffer s z 32 true ∧
        Buffer s b 32 false ∧ Buffer s e 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
        (b.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ b.toNat) ∧
        (e.toNat + 32 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ e.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xa8 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16) ∧
        Extracted.program.DataLoaded s.mem)
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s b 32) (valueAt s e 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xa8, (s.regs regSP).toNat + 0x20)]) :=
  Fv256.Amd64.EnsuresOfW.ensures3w 0x100 0xa8 0x20 0x20 (by decide) (by decide) Fv256.F.expSpec exp_summary z b e

end Fv256.Amd64.ExpMain
