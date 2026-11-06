import Fv256.Arm64.RecipDefs

/-!
# `Reciprocal` (arm64): statement of the library summary (Extracted-free; consumers take `RecipSummary` as a hypothesis)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg

/-- the 40-byte result `mu` (5 words, little endian) is written to the caller frame at `sp+8 .. sp+48`;
`sp`, `x18`, `x28`, `x29`, `x30` are as on entry; the frame window `[sp-280, sp+48)` is the only memory touched.
`mu = 0` below `2^192`, `RecipWeak` from `2^192`, `RecipOK` from `2^193` (m = the 32 bytes at `X0`). -/
def RecSpec (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 280, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] ∧
  (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192 → s'.mem.readLE (s.sp.toNat + 8) 40 = 0) ∧
  (2 ^ 192 ≤ s.mem.readLE (s.regs 0).toNat 32 →
    Fv256.F.RecipWeak (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
  (2 ^ 193 ≤ s.mem.readLE (s.regs 0).toNat 32 →
    Fv256.F.RecipOK (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE (s.sp.toNat + 8) 40))

/-- the summary to be proven (file `Fv256/Arm64/RecipSummary.lean`, theorem `recip_summary`) -/
def RecipSummary : Prop := Summary Fv256.Arm64.RecipProg.program recEntry RecPre RecSpec

end Fv256.Arm64.RecipSeg
