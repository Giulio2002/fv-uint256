import Fv256.ExpProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilB2
import Fv256.SpecF

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ExpSum

/-- entry of `(*Int).Exp` in the library program (0x4b9f00) -/
abbrev expEntry : Nat := 0x4b9f00

abbrev mulEntry : Nat := segAddr Fv256.ExpProg.program "github.com/holiman/uint256.(*Int).Mul"
abbrev sqEntry : Nat := segAddr Fv256.ExpProg.program "github.com/holiman/uint256.(*Int).squared"

/-- equal or disjoint 32-byte objects -/
def Al (p q : BitVec 64) : Prop := p = q ∨ p.toNat + 32 ≤ q.toNat ∨ q.toNat + 32 ≤ p.toNat

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem mul_summary :
    Summary Fv256.ExpProg.program mulEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        StackWritable s 16 8 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 16 ∨ (s.regs 4).toNat ≤ (s.regs 1).toNat))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = (s.mem.readLE (s.regs 3).toNat 32 * s.mem.readLE (s.regs 1).toNat 32) % 2 ^ 256 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 16, (s.regs 4).toNat + 8)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdz, hdx, hdy⟩
  simp only [regSP] at hacc hlow hnw
  have hx0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · janus64_simp
    refine Util.mul_limbs _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals (simp only [Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod])
    all_goals janus_carry
  · janus_frame

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem sq_summary :
    Summary Fv256.ExpProg.program sqEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        Buffer s (s.regs 0) 32 true ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat ∨ (s.regs 4).toNat + 8 ≤ (s.regs 0).toNat))
      (fun s s' => s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = (s.mem.readLE (s.regs 0).toNat 32 * s.mem.readLE (s.regs 0).toNat 32) % 2 ^ 256 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, ⟨hzw, hz⟩, hdz⟩
  have hx0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · janus64_simp
    refine Util.mul_limbs _ _ _ _ _ ?_ ?_ ?_ ?_
    all_goals (simp only [Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod])
    all_goals janus_carry
  · janus_frame

end Fv256.Amd64.ExpSum
