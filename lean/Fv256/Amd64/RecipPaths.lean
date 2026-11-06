import Fv256.Amd64.RecipEpi
import Fv256.Amd64.RecipSeg0
import Fv256.Amd64.LshNorm

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

theorem readLE_40 (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 40 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 +
      2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 := by
  rw [show 40 = 8 + 32 from rfl, Janus.Arm64.Memory.readLE_add, Util.readLE_32 m (a + 8)]
  simp only [Nat.add_assoc, Nat.mul_add]
  have e1 : a + 8 + 8 = a + 16 := by omega
  have e2 : a + 8 + 16 = a + 24 := by omega
  have e3 : a + 8 + 24 = a + 32 := by omega
  rw [e1, e2, e3]
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem path_m3z (s : State) (hpc : s.rip = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 = 0) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) s (fun s' =>
      s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
      s'.mem.readLE ((s.regs 4).toNat + 8) 40 = 0 ∧
      MemFrame s.mem s'.mem [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)]) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hsp
  janus64_run [Util.readLE_32, hm3]
  refine ⟨?_, ?_⟩
  · rw [readLE_40]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod]
  · repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := ((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)) (by simp) (by dsimp only; omega) (by dsimp only; omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem path_pow2 (s : State) (hpc : s.rip = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hp : ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)) :
    ReachesRet Fv256.RecipProg.program (retAddrOf s) s (fun s' =>
      s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
      s'.mem.readLE ((s.regs 4).toNat + 8) 40 =
        2 ^ 256 - 1 + 2 ^ 256 * ((2 ^ 64 - 1) / 2 ^ (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8))) ∧
      MemFrame s.mem s'.mem [((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)]) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hsp
  have hclz : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0 →
      Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 :=
    fun h => Fv256.Amd64.LshNorm.clz_le _ (Util.readLE8_lt _ _) h
  janus64_run [Util.readLE_32, hp, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.le_def, BitVec.lt_def,
    BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_eq, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]
  all_goals (
    have hcl := hclz hm3
    generalize Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) = c at *
    refine ⟨?_, ?_⟩
    · rw [readLE_40]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reduceMod, Nat.reducePow]
      have e : (63 - c) % 64 = 63 - c := by omega
      by_cases h0 : 63 - c = 0
      · rw [h0] <;> omega
      · first
          | (exfalso; omega)
          | (rw [e]
             have hq : 18446744073709551615 / 2 ^ (63 - c) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
             generalize 18446744073709551615 / 2 ^ (63 - c) = q at *
             omega)
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := ((s.regs 4).toNat - 576, (s.regs 4).toNat + 48)) (by simp) (by dsimp only; omega) (by dsimp only; omega))

end Fv256.Amd64.RecipSeg
