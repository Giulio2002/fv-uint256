import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.AddModF
import Fv256.Arm64.AddModComp2

/-!
# `(*uint256.Int).AddMod(x, y, m *Int) *Int` (arm64): `z = (x + y) mod m` (`0` when `m = 0`)

**Documented behaviour.** "AddMod sets z to the sum ( x+y ) mod m, and returns z. If m == 0, z is set to 0 (OBS: differs from the big.Int)".
The spec is `Fv256.F.addmodSpec` (full-precision `(x+y) mod m`, `0` for `m = 0`).

**Guarantee.** For all pointers `z` (`X0`), `x` (`X1`), `y` (`X2`), `m` (`X3`) with the 32 bytes at `z` writable and the others
readable (all below `2^48`), none overlapping the callee window `[SP-856, SP+16)`, `z` equal to or disjoint from each of `x`,
`y`, `m` (the others may overlap each other arbitrarily), the stack-growth checks falling through (`GuardOK s 816`), the read-only
data of the binary loaded, and `stackguard0` not overlapping `z`: the call returns (no fault, no panic), obeys the ABI, returns
`z` in `X0`, the number at `z` afterwards is `addmodSpec` of the numbers at `x`, `y`, `m` before the call, and nothing changes
outside `z[0..32)` and the window.

Structure: the fast path (`m[3] ≠ 0` and `x[3], y[3] ≤ m[3]`) is `AddModF.addmod_fast` (twelve carry-chain shape closers);
the generic path is the composition of small segments `AddModSeg`/`AddModSegB`/`AddModSegZ` in `AddModComp2.gen_all`
(callees `Mod` via `ModSum` and `udivrem` via `UdivremFinal`, both library summaries).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddMod

theorem addmod_summary : Summary Extracted.program Extracted.entry Fv256.Arm64.AddModSeg.PreS
    (fun s s' => Fv256.Arm64.AddModComp2.Post s s') := by
  intro s hpc hpre
  by_cases hf : (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧
      s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8)
  · exact Fv256.Arm64.AddModF.addmod_fast s hpc ⟨hpre, hf⟩
  · exact Fv256.Arm64.AddModComp2.gen_all s hpc hpre hf

end Fv256.Arm64.AddMod
