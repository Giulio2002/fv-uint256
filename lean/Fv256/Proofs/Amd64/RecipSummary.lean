import Fv256.Proofs.Amd64.RecipMain

/-!
# `Reciprocal` (amd64): the whole-function summary over the Extracted-free `Fv256.RecipProg`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.F

namespace Fv256.Amd64.RecipSeg

theorem model_pow2 (s : State) (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hnp : ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)) :
    recipModel (s.mem.readLE (s.regs 0).toNat 32) =
      2 ^ 256 - 1 + 2 ^ 256 * ((2 ^ 64 - 1) / 2 ^ (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8))) := by
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hpw := (pow2_test _ _ _ _ bb0 bb1 bb2 bb3 hm3).1 hnp
  have hm192 : ¬ (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192) := by
    rw [m_limbs s]
    have : 0 < s.mem.readLE ((s.regs 0).toNat + 24) 8 := Nat.pos_of_ne_zero hm3
    omega
  rw [m_limbs s] at hm192 ⊢
  unfold recipModel
  rw [if_neg hm192, if_pos hpw]
  unfold recipPow2
  rw [log2_split _ _ _ _ bb0 bb1 bb2 bb3 hm3, clz_log2 _ bb3 hm3]
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

/-- the machine-level summary: the result words equal the pure-Nat model -/
theorem recip_model_summary : Summary Fv256.RecipProg.program recEntry RecPre
    (fun s s' => RecPost s s' (recipModel (s.mem.readLE (s.regs 0).toNat 32))) := by
  intro s hpc hpre
  by_cases hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 = 0
  · refine Fv256.SegCompose.seg_mono (path_m3z s hpc hpre hm3) ?_
    intro s' ⟨e4, e5, e14, e15, hmu, hfr⟩
    exact ⟨e4, e5, e14, e15, by rw [hmu, model_m3z s hm3], hfr⟩
  · by_cases hnp : ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)
    · refine Fv256.SegCompose.seg_mono (path_pow2 s hpc hpre hm3 hnp) ?_
      intro s' ⟨e4, e5, e14, e15, hmu, hfr⟩
      exact ⟨e4, e5, e14, e15, by rw [hmu, model_pow2 s hm3 hnp], hfr⟩
    · exact main_path s hpc hpre hm3 hnp

/-- the specification of `Reciprocal`: `mu = 0` below `2^192`; `RecipWeak` from `2^192`; `RecipOK` from `2^193` -/
def RecSpec (s s' : State) : Prop :=
  s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
  MemFrame s.mem s'.mem [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)] ∧
  (s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 192 → s'.mem.readLE ((s.regs 4).toNat + 8) 40 = 0) ∧
  (2 ^ 192 ≤ s.mem.readLE (s.regs 0).toNat 32 → RecipWeak (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE ((s.regs 4).toNat + 8) 40)) ∧
  (2 ^ 193 ≤ s.mem.readLE (s.regs 0).toNat 32 → RecipOK (s.mem.readLE (s.regs 0).toNat 32) (s'.mem.readLE ((s.regs 4).toNat + 8) 40))

theorem recip_summary : Summary Fv256.RecipProg.program recEntry RecPre RecSpec := by
  intro s hpc hpre
  refine Fv256.SegCompose.seg_mono (recip_model_summary s hpc hpre) ?_
  intro s' ⟨e4, e5, e14, e15, hmu, hfr⟩
  have bb0 := Util.readLE8_lt s.mem (s.regs 0).toNat
  have bb1 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 8)
  have bb2 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 16)
  have bb3 := Util.readLE8_lt s.mem ((s.regs 0).toNat + 24)
  have hlt : s.mem.readLE (s.regs 0).toNat 32 < 2 ^ 256 := by rw [m_limbs s]; omega
  refine ⟨e4, e5, e14, e15, hfr, ?_, ?_, ?_⟩
  · intro h; rw [hmu]; exact recip_lt192 _ h
  · intro h; rw [hmu]; exact (recip_chain _ h hlt).1
  · intro h; rw [hmu]; exact (recip_chain _ (by omega) hlt).2 h

end Fv256.Amd64.RecipSeg
