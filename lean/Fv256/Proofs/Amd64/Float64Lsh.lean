import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Float64

abbrev lshEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"

/-- `Lsh(z, x, n)` as a callee on amd64 (`z` in `RAX`, `x` in `RBX`, `n` in `RCX`, return address at `[RSP]`),
`z` and `x` disjoint 32-byte objects, the return-address slot disjoint from `z`. DRAFT: statement only, proof pending the
amd64 Float64 workspace (port of the disjoint branch of `Fv256.Amd64.Lsh.correctness`). -/
def LshSummary (z x : BitVec 64) : Prop :=
  Summary Extracted.program lshEntry
    (fun s => s.regs 0 = z ∧ s.regs 3 = x ∧
      (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
      Buffer s z 32 true ∧ Buffer s x 32 false ∧
      Disjoint z 32 (s.regs 4) 8 ∧ Disjoint z 32 x 32)
    (fun s s' => s'.regs 0 = z ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
      s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
      valueAt s' z 32 = Spec.lsh (valueAt s x 32) (s.regs 1).toNat ∧
      MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)])

end Fv256.Amd64.Float64
