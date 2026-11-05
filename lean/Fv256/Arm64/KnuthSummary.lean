import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Arm64.KnuthDefs
import Fv256.Arm64.Div64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthDefs
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthSummary
abbrev kn : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

/-- `udivremKnuth(quot, u, d []uint64)` (arm64 ABI: quot = X0/X1/X2, u = X3/X4/X5, d = X6/X7/X8). Let `m = len u = X4`,
`n = len d = X7`, `ql = len quot = X1`, `cap = cap u = X5`. Precondition: `2 <= n <= m < 2^20`, `m <= cap < 2^55`, `m - n <= ql < 2^20`,
the top word of `d` is normalised (`>= 2^63`), the top `n` words of `u` are `< d`. Postcondition: `u = d * quot + u'`, `u' < d`
(`u'` = the low `n` words of `u` afterwards). -/
theorem knuth_summary :
    Summary Extracted.program kn
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 80 ∧ StackOK s 120 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        2 ≤ (s.regs 7).toNat ∧ (s.regs 7).toNat ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat < 2 ^ 20 ∧
        (s.regs 4).toNat ≤ (s.regs 5).toNat ∧ (s.regs 5).toNat < 2 ^ 55 ∧
        (s.regs 4).toNat - (s.regs 7).toNat ≤ (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 20 ∧
        (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * (s.regs 4).toNat) true = true ∧
        (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat (8 * (s.regs 7).toNat) false = true ∧
        (s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * (s.regs 1).toNat) true = true ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 6).toNat ∨ (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        2 ^ 63 ≤ s.mem.readLE ((s.regs 6).toNat + 8 * ((s.regs 7).toNat - 1)) 8 ∧
        Fv256.B.wv s.mem ((s.regs 3).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)) (s.regs 7).toNat <
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧ (∀ i, 22 ≤ i → s'.regs i = s.regs i) ∧
        Fv256.B.wv s.mem (s.regs 3).toNat (s.regs 4).toNat =
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat * Fv256.B.wv s'.mem (s.regs 0).toNat ((s.regs 4).toNat - (s.regs 7).toNat) +
            Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat ∧
        Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat < Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 3).toNat, (s.regs 3).toNat + 8 * (s.regs 4).toNat),
          ((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)),
          (s.sp.toNat - 120, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]) := by
  sorry

end Fv256.Arm64.KnuthSummary
