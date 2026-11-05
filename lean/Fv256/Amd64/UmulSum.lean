import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.UmulSum

abbrev umulEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.umul"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
set_option exponentiation.threshold 600 in
theorem umul_summary :
    Summary Extracted.program umulEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        StackWritable s 0x30 0x18 ∧
        Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 0) 32 false ∧ Buffer s (s.regs 1) 64 true ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x30 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 3).toNat) ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x30 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 64 ≤ (s.regs 4).toNat - 0x30 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 1).toNat) ∧
        ((s.regs 1).toNat + 64 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat) ∧
        ((s.regs 1).toNat + 64 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 1).toNat))
      (fun s s' => s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        Fv256.B.wv s'.mem (s.regs 1).toNat 8 = s.mem.readLE (s.regs 0).toNat 32 * s.mem.readLE (s.regs 3).toNat 32 ∧
        MemFrame s.mem s'.mem [((s.regs 1).toNat, (s.regs 1).toNat + 64), ((s.regs 4).toNat - 0x30, (s.regs 4).toNat + 0x18)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, ⟨hlow, hnw, hacc⟩, ⟨hyw, hy⟩, ⟨hxw, hx⟩, ⟨hrw, hr⟩, hdy, hdx, hdr, hrx, hry⟩
  simp only [regSP] at hacc hlow hnw
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · simp (disch := omega) only [Fv256.B.wv_succ, Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self]
    have hx := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 0).toNat 32
    have hy := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 32
    refine Fv256.F.mul8_limbs' _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [Util.readLE_32] at hx hy
      have := Nat.mul_lt_mul'' hx hy
      omega
    all_goals (simp only [Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod])
    all_goals (first | janus_carry | (trace_state; sorry))
  · janus_frame

end Fv256.Amd64.UmulSum
