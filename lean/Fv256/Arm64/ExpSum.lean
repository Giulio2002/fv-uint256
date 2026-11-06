import Fv256.Arm64.ExpProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF

/-!
# Library summaries of the leaves of `Exp` (arm64): `(*Int).Mul` and `(*Int).squared`, over `ExpProg.program` (Extracted-free)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ExpSum

abbrev expEntry : Nat := segAddr Fv256.Arm64.ExpProg.program "github.com/holiman/uint256.(*Int).Exp"
abbrev mulEntry : Nat := segAddr Fv256.Arm64.ExpProg.program "github.com/holiman/uint256.(*Int).Mul"
abbrev sqEntry : Nat := segAddr Fv256.Arm64.ExpProg.program "github.com/holiman/uint256.(*Int).squared"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem mul_summary :
    Summary Fv256.Arm64.ExpProg.program mulEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        s.regs 1 = s.regs 0 ∧ Disjoint32 (s.regs 0).toNat (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Spec.mul (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) := by
  intro s hpc ⟨h30a, h30b, hzb, hza, hxb, hxa, hyb, hya, hzx, hzy⟩
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have hz0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have hz1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have hz2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have hz3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  simp only [Disjoint32, Disjoint] at hzy
  janus_run [Util.readLE_32, hzx]
  simp only [Spec.mul, Spec.W, Nat.reducePow]
  refine ⟨?_, ?_⟩
  · janus_arith
  · janus_frame

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem sq_summary :
    Summary Fv256.Arm64.ExpProg.program sqEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Spec.mul (s.mem.readLE (s.regs 0).toNat 32) (s.mem.readLE (s.regs 0).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) := by
  intro s hpc ⟨h30a, h30b, hzb, hza⟩
  have hz0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have hz1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have hz2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have hz3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  janus_run [Util.readLE_32]
  simp only [Spec.mul, Spec.W, Nat.reducePow]
  refine ⟨?_, ?_⟩
  · janus_arith
  · janus_frame

end Fv256.Arm64.ExpSum
