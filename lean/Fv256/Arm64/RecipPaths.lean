import Fv256.Arm64.RecipSeg0

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.RecipSeg

/-- common shape of a completed run: registers, the frame, the 40-byte result -/
def RecPost (s s' : State) (mu : Nat) : Prop :=
  s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 280, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)] ∧
  s'.mem.readLE (s.sp.toNat + 8) 40 = mu

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
theorem path_m3z (s : State) (hpc : s.pc = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 = 0) :
    ReachesRet Fv256.Arm64.RecipProg.program (s.regs 30) s (fun s' => RecPost s s' 0) := by
  have hpre' := hpre
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hpre
  janus_run [hm3]
  all_goals (
    unfold RecPost
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 280, s.sp.toNat - 8)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat + 8, s.sp.toNat + 48)) (by simp) (by omega) (by omega)
    · rw [readLE_40]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_div, Nat.zero_mod])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem path_pow2 (s : State) (hpc : s.pc = BitVec.ofNat 64 recEntry) (hpre : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hz : (s.mem.readLE ((s.regs 0).toNat + 24) 8 &&& s.mem.readLE ((s.regs 0).toNat + 24) 8 - 1 |||
      (s.mem.readLE ((s.regs 0).toNat + 16) 8 ||| (s.mem.readLE ((s.regs 0).toNat + 8) 8 ||| s.mem.readLE (s.regs 0).toNat 8))) = 0) :
    ReachesRet Fv256.Arm64.RecipProg.program (s.regs 30) s (fun s' => RecPost s s'
      (2 ^ 256 - 1 + 2 ^ 256 * ((2 ^ 64 - 1) / 2 ^ (63 - clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8))))) := by
  have hpre' := hpre
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hpre
  have hclz : clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) ≤ 63 :=
    Fv256.Arm64.RecipNat.clz_le _ (Util.readLE8_lt _ _) hm3
  janus_run [hz]
  all_goals (
    generalize clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) = c at *
    unfold RecPost
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · simp [setReg]
    · repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat - 280, s.sp.toNat - 8)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (s.sp.toNat + 8, s.sp.toNat + 48)) (by simp) (by omega) (by omega)
    · rw [readLE_40]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reduceMod, Nat.reducePow, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      have e : ((18446744073709551616 - c + 64) % 18446744073709551616 + 191) % 64 = 63 - c := by omega
      rw [e, Nat.shiftRight_eq_div_pow]
      have hq : 18446744073709551615 / 2 ^ (63 - c) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by decide)
      rw [Nat.mod_eq_of_lt hq])

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- epilogue: `ldp x29,x30; add sp; ret` -/
theorem g_epi (s S : State) (hpc : S.pc = BitVec.ofNat 64 (recEntry + 0x77c)) (hpre : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem) :
    ReachesRet Fv256.Arm64.RecipProg.program (s.regs 30) S (fun S' =>
      S'.sp = s.sp ∧ S'.regs 18 = s.regs 18 ∧ S'.regs 28 = s.regs 28 ∧ S'.regs 29 = s.regs 29 ∧ S'.regs 30 = s.regs 30 ∧ S'.mem = S.mem) := by
  obtain ⟨h1, h2, ⟨hg1, hg2, hg3⟩, ⟨hsa, hsb, hsc, hsd⟩, hgw, hm1, hm2, hmd⟩ := hpre
  obtain ⟨hr1, hr2, hr3, hr4⟩ := hR
  obtain ⟨hm29, hm30, hfr⟩ := hM
  have hS := RecRegs.sp_toNat ⟨hr1, hr2, hr3, hr4⟩ hsb
  have hsp : S.sp.toNat = s.sp.toNat - 272 := by omega
  janus_run [hm29, hm30, hsp]

end Fv256.Arm64.RecipSeg
