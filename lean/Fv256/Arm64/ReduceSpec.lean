import Fv256.SpecF
import Fv256.MulModMath
import Fv256.Arm64.ReduceProg

/-!
# `(*Int).reduce4` (arm64): the summary statement (shared by the reduce4 proof and by the `MulMod` / `MulModWithReciprocal` glue)

`z.reduce4(x *[8]uint64, m *Int, mu *[5]uint64)`: `X0 = z`, `X1 = x` (64 bytes), `X2 = m` (32 bytes, `m[3] != 0`), `X3 = mu` (40 bytes,
`RecipWeak m mu`).  Result: the 32 bytes at `z` are `x mod m`.  The frame window is `[SP-168, SP+16)` (the callee spills `x0` at `SP+8`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ReduceSpec

abbrev r4Entry : Nat := segAddr Fv256.Arm64.ReduceProg.program "github.com/holiman/uint256.(*Int).reduce4"

abbrev R4Pre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0x20 ∧ StackOK s 168 16 ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
  ((s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
    ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat)) ∧
  ((s.regs 1).toNat + 64 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 64 false = true ∧
    ((s.regs 1).toNat + 64 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat)) ∧
  ((s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
    ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat)) ∧
  ((s.regs 3).toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 40 false = true ∧
    ((s.regs 3).toNat + 40 ≤ s.sp.toNat - 168 ∨ s.sp.toNat + 16 ≤ (s.regs 3).toNat)) ∧
  s.mem.readLE ((s.regs 2).toNat + 24) 8 ≠ 0 ∧
  Fv256.F.RecipWeak (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 40)

abbrev R4Post (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.sp - 8#64 ∧ s'.regs 30 = s.regs 30 ∧
  (∀ i, i ∉ [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26] → i = 0 ∨ i = 29 ∨ s'.regs i = s.regs i) ∧
  s'.mem.readLE (s.regs 0).toNat 32 = s.mem.readLE (s.regs 1).toNat 64 % s.mem.readLE (s.regs 2).toNat 32 ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat), (s.sp.toNat + 8, s.sp.toNat + 16)]

/-- the library summary of `reduce4` (the target of the arm64 proof; consumed by the `MulMod` glue through `lib_summary`) -/
def R4Summary : Prop := Summary Fv256.Arm64.ReduceProg.program r4Entry R4Pre R4Post

end Fv256.Arm64.ReduceSpec
