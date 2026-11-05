import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.UmulSum

abbrev umulEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.umul"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
set_option exponentiation.threshold 600 in
theorem umul_summary :
    Summary Extracted.program umulEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 false = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 64 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 64 true = true ∧
        ((s.regs 2).toNat + 64 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 2).toNat) ∧
        ((s.regs 2).toNat + 64 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 2).toNat))
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        Fv256.B.wv s'.mem (s.regs 2).toNat 8 = s.mem.readLE (s.regs 0).toNat 32 * s.mem.readLE (s.regs 1).toNat 32 ∧
        MemFrame s.mem s'.mem [((s.regs 2).toNat, (s.regs 2).toNat + 64)]) := by
  intro s hpc ⟨h30a, h30b, hxw, hx, hyw, hy, hrw, hr, hrx, hry⟩
  janus_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · simp (disch := omega) only [Fv256.B.wv_succ, Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 32
    have hy := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 32
    refine Fv256.F.mul8_limbs' _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Util.readLE_32] at hx hy
      have := Nat.mul_lt_mul'' hx hy
      omega
    all_goals (simp only [Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod])
    all_goals janus_carry
  · janus_frame

end Fv256.Arm64.UmulSum
