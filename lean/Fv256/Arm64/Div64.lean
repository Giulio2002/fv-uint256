import Extracted
import Fv256.Spec

/-!
# `math/bits.Div64(hi, lo, y uint64) (quo, rem uint64)` (arm64)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Div64

abbrev d64 : Nat := segAddr Extracted.program "math/bits.Div64"

set_option maxHeartbeats 16000000 in
theorem div64_summary :
    Summary Extracted.program d64
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0 ∧ StackOK s 40 0 ∧
        (s.regs 2).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        (s'.regs 0).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat ∧
        (s'.regs 1).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → s'.regs i = s.regs i) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hy, hhi⟩
  janus_run
  all_goals sorry

end Fv256.Arm64.Div64
