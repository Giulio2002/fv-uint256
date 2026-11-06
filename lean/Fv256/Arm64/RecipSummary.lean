import Fv256.Arm64.RecipMain
import Fv256.Arm64.RecipSpecA
import Fv256.RecipChain

/-!
# `Reciprocal` (arm64): the whole-function summary over the Extracted-free `Fv256.Arm64.RecipProg`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.F

namespace Fv256.Arm64.RecipSeg

theorem model_pow2 (s : State) (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hz : (s.mem.readLE ((s.regs 0).toNat + 24) 8 &&& s.mem.readLE ((s.regs 0).toNat + 24) 8 - 1 |||
      (s.mem.readLE ((s.regs 0).toNat + 16) 8 ||| (s.mem.readLE ((s.regs 0).toNat + 8) 8 ||| s.mem.readLE (s.regs 0).toNat 8))) = 0) :
    recipModel (s.mem.readLE (s.regs 0).toNat 32) =
      2 ^ 256 - 1 + 2 ^ 256 * ((2 ^ 64 - 1) / 2 ^ (63 - clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8))) := by
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hpw := (pow2_nat _ _ _ _ bb0 bb1 bb2 bb3 hm3).1 hz
  have hm192 : ¬ (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192) := by
    rw [m_limbs s]
    have : 0 < s.mem.readLE ((s.regs 0).toNat + 24) 8 := Nat.pos_of_ne_zero hm3
    omega
  rw [m_limbs s] at hm192 ⊢
  unfold recipModel
  rw [if_neg hm192, if_pos hpw]
  unfold recipPow2
  rw [Fv256.Arm64.RecipBridge.log2_split _ _ _ _ bb0 bb1 bb2 bb3 hm3, Fv256.Arm64.RecipBridge.clz_log2 _ bb3 hm3]
  have hl : Nat.log2 (s.mem.readLE ((s.regs 0).toNat + 24) 8) < 64 := by rw [Nat.log2_lt hm3]; exact bb3
  have e1 : (192 + Nat.log2 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) % 64 = Nat.log2 (s.mem.readLE ((s.regs 0).toNat + 24) 8) := by omega
  have e2 : 63 - (63 - Nat.log2 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) = Nat.log2 (s.mem.readLE ((s.regs 0).toNat + 24) 8) := by omega
  rw [e1, e2]

theorem model_m3z (s : State) (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 = 0) :
    recipModel (s.mem.readLE (s.regs 0).toNat 32) = 0 := by
  apply recip_lt192
  rw [m_limbs s, hm3]
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  omega

theorem recip_model_summary : Summary Fv256.Arm64.RecipProg.program recEntry RecPre
    (fun s s' => RecPost s s' (recipModel (s.mem.readLE (s.regs 0).toNat 32))) := by
  intro s hpc hpre
  by_cases hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 = 0
  · refine Fv256.Arm64.SegCompose.seg_mono (path_m3z s hpc hpre hm3) ?_
    intro s' ⟨e1, e2, e3, e4, e5, hfr, hmu⟩
    exact ⟨e1, e2, e3, e4, e5, hfr, by rw [hmu, model_m3z s hm3]⟩
  · by_cases hz : (s.mem.readLE ((s.regs 0).toNat + 24) 8 &&& s.mem.readLE ((s.regs 0).toNat + 24) 8 - 1 |||
      (s.mem.readLE ((s.regs 0).toNat + 16) 8 ||| (s.mem.readLE ((s.regs 0).toNat + 8) 8 ||| s.mem.readLE (s.regs 0).toNat 8))) = 0
    · refine Fv256.Arm64.SegCompose.seg_mono (path_pow2 s hpc hpre hm3 hz) ?_
      intro s' ⟨e1, e2, e3, e4, e5, hfr, hmu⟩
      exact ⟨e1, e2, e3, e4, e5, hfr, by rw [hmu, model_pow2 s hm3 hz]⟩
    · exact main_path s hpc hpre hm3 hz

theorem recip_summary : RecipSummary := by
  intro s hpc hpre
  refine Fv256.Arm64.SegCompose.seg_mono (recip_model_summary s hpc hpre) ?_
  intro s' ⟨e1, e2, e3, e4, e5, hfr, hmu⟩
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hlt : s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 256 := by rw [m_limbs s]; omega
  refine ⟨e1, e2, e3, e4, e5, hfr, ?_, ?_, ?_⟩
  · intro h; rw [hmu]; exact recip_lt192 _ h
  · intro h; rw [hmu]; exact (recip_chain _ h hlt).1
  · intro h; rw [hmu]; exact (recip_chain _ (by omega) hlt).2 h

end Fv256.Arm64.RecipSeg
