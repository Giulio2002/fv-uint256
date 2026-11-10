import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Amd64.SqrtLibBase
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.SqrtMath
import Fv256.Proofs.Common.SqrtHead
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Amd64.SqrtBigL
import Fv256.Proofs.Amd64.SqrtLoopL
import Fv256.Proofs.Common.SqrtTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SqrtLib

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem sqrt_big1 :
    Summary Fv256.SqrtProg.program Fv256.Amd64.SqrtLib.sqrtEntry
      (fun s => SPre s ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 8) 8 ≠ 0)
      SPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, hz2, hz3, hxj⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hz2, hz3, hxj] until [Fv256.Amd64.SqrtLib.sqrtEntry + 0x205]
    calls [Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSumA.lsh_summary_alias (s.regs 4 - 40#64)),
           Fv256.CodeIn.lib_summary hcRsh (Fv256.Amd64.RshSum.rsh_summary (s.regs 4 - 72#64) (s.regs 3))]
  all_goals grab_const Fv256.Spec.lsh as hLv
  all_goals grab_const Fv256.Spec.rsh as hRv
  all_goals grab_frame 40 as hLf
  all_goals grab_frame 72 as hRf
  all_goals have hxb : s.mem.readLE ((s.regs 3).toNat + 8) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  all_goals (simp only [valueAt, Util.readLE_32] at hLv hRv)
  all_goals (simp only [hs40, hs72] at hLv hRv)
  all_goals (simp (disch := omega) only [valueAt, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside] at hLv hRv)
  have hl0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hl1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hl2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hl3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 3).toNat + 8) 8) = k := ⟨_, rfl⟩
  have hbl := Fv256.B.f64_bl1 (s.mem.readLE (s.regs 3).toNat 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) k hl0 hl1 hxj hk
  have hkj : k < 64 := by have := Util.clz_bl 64 (s.mem.readLE ((s.regs 3).toNat + 8) 8) hl1; have := SqrtHead.bl_pos _ hxj; omega
  rw [hk] at hLv hRv
  have hcl : ((BitVec.ofNat 64 (63 - k) + 66#64) >>> 1).toNat = (63 - k + 66) / 2 := SqrtHead.shr1_add (63 - k) 66 (by omega)
  rw [hcl] at hLv hRv
  have harith := SqrtHead.head_arith _ (128 - k) ((63 - k + 66) / 2) hbl (by omega) (by omega) (by omega)
  obtain ⟨hc1, hc128, hXinv, hX64, hX256⟩ := harith
  simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, show (256 : Nat) ^ 8 = 2 ^ 64 by decide,
    Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)] at hLv
  have hlsh : Spec.lsh 1 ((63 - k + 66) / 2) = 2 ^ ((63 - k + 66) / 2) := by
    unfold Spec.lsh
    try unfold Spec.W
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
  rw [hlsh] at hLv
  simp (disch := (simp [Outside]; omega)) only [hLf.readLE] at hRv
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_inside] at hRv
  have hsumA : s'.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 +
      2 ^ 128 * s'.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = 2 ^ ((63 - k + 66) / 2) := by
    rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
      hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hLv
  have hXeq : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have hr0 : s'.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  grab_proj_of hRf regs 4 as hs4
  grab_proj_of hRf regs 5 as hs5
  grab_proj_of hRf regs 14 as hs14
  grab_proj_of hRf xmm 15 as hsx
  grab_proj_of hLf regs 14 as hl14
  grab_proj_of hLf regs 5 as hl5
  grab_proj_of hLf xmm 15 as hlx
  have hXs : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 2 ^ 128 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have f1 : (s.regs 4).toNat - 72 + 8 = (s.regs 4).toNat - 64 := by omega
  have f2 : (s.regs 4).toNat - 72 + 16 = (s.regs 4).toNat - 56 := by omega
  have f3 : (s.regs 4).toNat - 72 + 24 = (s.regs 4).toNat - 48 := by omega
  have g1 : (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 := by omega
  have g2 : (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 := by omega
  have g3 : (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 := by omega
  simp only [f1, f2, f3, ← hXs, Spec.rsh] at hRv
  simp only [g1, g2, g3] at hsumA
  refine big_loop s (s.mem.readLE (s.regs 3).toNat 32) (s.regs 0) (s.regs 3) (SPost s) (by omega) (by omega) hra2 hdz hdx hdg hgb hnw2 hgr hsp (by omega)
    (fun r S' hsq h0 h4 h5 h14 hx15' hdf hmx hr hfr => ⟨h0, h4, h5, h14, by rw [hx15', hx15], hdf, hmx, by rw [hr]; exact hsq, hfr⟩)
    (2 ^ ((63 - k + 66) / 2)) (s'.mem.readLE ((s.regs 4).toNat - 40) 8) (s'.mem.readLE ((s.regs 4).toNat - 32) 8) (s'.mem.readLE ((s.regs 4).toNat - 24) 8) (s'.mem.readLE ((s.regs 4).toNat - 16) 8)
    (s'.mem.readLE ((s.regs 4).toNat - 72) 8) (s'.mem.readLE ((s.regs 4).toNat - 64) 8) (s'.mem.readLE ((s.regs 4).toNat - 56) 8) (s'.mem.readLE ((s.regs 4).toNat - 48) 8)
    _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) (by rw [hXeq]; rw [hz2]; rw [hz3];  exact hXinv) ?hXm
  case hXm =>
    rw [Util.readLE_32]
    simp (disch := (simp [Outside]; omega)) only [hRf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    simp (disch := (simp [Outside]; omega)) only [hLf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hXs.symm
  case inv =>
    refine ⟨?rip, ?r4, ?r5, ?r14, ?x15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?msav, ?mz, ?mx,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?hwin, ?hxacc, ?hzacc, hzw, hxw, ?hfrm⟩
    case rip => show (4957573#64 : BitVec 64) = BitVec.ofNat 64 headB; decide
    case r4 => rw [hs4]; simp [setRegF, sub144]
    case r5 => rw [hs5]; simp [setRegF, hl5]
    case r14 => rw [hs14]; simp [setRegF, hl14]
    case x15 => rw [hsx]; simp [hlx, hx15]
    case mret => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
    case msav => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 5); omega
    case mz => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 0); omega
    case mx => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 3); omega
    case hwin => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
    case hxacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hx
    case hzacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hz
    case hfrm =>
      refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)])
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?A1 hLf ?s11)
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?B1 hRf ?s21) ?s31
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · intro a n h; simp [Outside] at h ⊢; omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem sqrt_big2 :
    Summary Fv256.SqrtProg.program Fv256.Amd64.SqrtLib.sqrtEntry
      (fun s => SPre s ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 ≠ 0)
      SPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, hz3, hxj⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hz3, hxj] until [Fv256.Amd64.SqrtLib.sqrtEntry + 0x205]
    calls [Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSumA.lsh_summary_alias (s.regs 4 - 40#64)),
           Fv256.CodeIn.lib_summary hcRsh (Fv256.Amd64.RshSum.rsh_summary (s.regs 4 - 72#64) (s.regs 3))]
  all_goals grab_const Fv256.Spec.lsh as hLv
  all_goals grab_const Fv256.Spec.rsh as hRv
  all_goals grab_frame 40 as hLf
  all_goals grab_frame 72 as hRf
  all_goals have hxb : s.mem.readLE ((s.regs 3).toNat + 8) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  all_goals (simp only [valueAt, Util.readLE_32] at hLv hRv)
  all_goals (simp only [hs40, hs72] at hLv hRv)
  all_goals (simp (disch := omega) only [valueAt, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside] at hLv hRv)
  have hl0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hl1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hl2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hl3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 3).toNat + 16) 8) = k := ⟨_, rfl⟩
  have hbl := Fv256.B.f64_bl2 (s.mem.readLE (s.regs 3).toNat 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 16) 8) k hl0 hl1 hl2 hxj hk
  have hkj : k < 64 := by have := Util.clz_bl 64 (s.mem.readLE ((s.regs 3).toNat + 16) 8) hl2; have := SqrtHead.bl_pos _ hxj; omega
  rw [hk] at hLv hRv
  have hcl : ((BitVec.ofNat 64 (63 - k) + 130#64) >>> 1).toNat = (63 - k + 130) / 2 := SqrtHead.shr1_add (63 - k) 130 (by omega)
  rw [hcl] at hLv hRv
  have harith := SqrtHead.head_arith _ (192 - k) ((63 - k + 130) / 2) hbl (by omega) (by omega) (by omega)
  obtain ⟨hc1, hc128, hXinv, hX64, hX256⟩ := harith
  simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, show (256 : Nat) ^ 8 = 2 ^ 64 by decide,
    Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)] at hLv
  have hlsh : Spec.lsh 1 ((63 - k + 130) / 2) = 2 ^ ((63 - k + 130) / 2) := by
    unfold Spec.lsh
    try unfold Spec.W
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
  rw [hlsh] at hLv
  simp (disch := (simp [Outside]; omega)) only [hLf.readLE] at hRv
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_inside] at hRv
  have hsumA : s'.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 +
      2 ^ 128 * s'.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = 2 ^ ((63 - k + 130) / 2) := by
    rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
      hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hLv
  have hXeq : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have hr0 : s'.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  grab_proj_of hRf regs 4 as hs4
  grab_proj_of hRf regs 5 as hs5
  grab_proj_of hRf regs 14 as hs14
  grab_proj_of hRf xmm 15 as hsx
  grab_proj_of hLf regs 14 as hl14
  grab_proj_of hLf regs 5 as hl5
  grab_proj_of hLf xmm 15 as hlx
  have hXs : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 2 ^ 128 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have f1 : (s.regs 4).toNat - 72 + 8 = (s.regs 4).toNat - 64 := by omega
  have f2 : (s.regs 4).toNat - 72 + 16 = (s.regs 4).toNat - 56 := by omega
  have f3 : (s.regs 4).toNat - 72 + 24 = (s.regs 4).toNat - 48 := by omega
  have g1 : (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 := by omega
  have g2 : (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 := by omega
  have g3 : (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 := by omega
  simp only [f1, f2, f3, ← hXs, Spec.rsh] at hRv
  simp only [g1, g2, g3] at hsumA
  refine big_loop s (s.mem.readLE (s.regs 3).toNat 32) (s.regs 0) (s.regs 3) (SPost s) (by omega) (by omega) hra2 hdz hdx hdg hgb hnw2 hgr hsp (by omega)
    (fun r S' hsq h0 h4 h5 h14 hx15' hdf hmx hr hfr => ⟨h0, h4, h5, h14, by rw [hx15', hx15], hdf, hmx, by rw [hr]; exact hsq, hfr⟩)
    (2 ^ ((63 - k + 130) / 2)) (s'.mem.readLE ((s.regs 4).toNat - 40) 8) (s'.mem.readLE ((s.regs 4).toNat - 32) 8) (s'.mem.readLE ((s.regs 4).toNat - 24) 8) (s'.mem.readLE ((s.regs 4).toNat - 16) 8)
    (s'.mem.readLE ((s.regs 4).toNat - 72) 8) (s'.mem.readLE ((s.regs 4).toNat - 64) 8) (s'.mem.readLE ((s.regs 4).toNat - 56) 8) (s'.mem.readLE ((s.regs 4).toNat - 48) 8)
    _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) (by rw [hXeq]; rw [hz3];  exact hXinv) ?hXm
  case hXm =>
    rw [Util.readLE_32]
    simp (disch := (simp [Outside]; omega)) only [hRf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    simp (disch := (simp [Outside]; omega)) only [hLf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hXs.symm
  case inv =>
    refine ⟨?rip, ?r4, ?r5, ?r14, ?x15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?msav, ?mz, ?mx,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?hwin, ?hxacc, ?hzacc, hzw, hxw, ?hfrm⟩
    case rip => show (4957573#64 : BitVec 64) = BitVec.ofNat 64 headB; decide
    case r4 => rw [hs4]; simp [setRegF, sub144]
    case r5 => rw [hs5]; simp [setRegF, hl5]
    case r14 => rw [hs14]; simp [setRegF, hl14]
    case x15 => rw [hsx]; simp [hlx, hx15]
    case mret => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
    case msav => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 5); omega
    case mz => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 0); omega
    case mx => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 3); omega
    case hwin => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
    case hxacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hx
    case hzacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hz
    case hfrm =>
      refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)])
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?A2 hLf ?s12)
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?B2 hRf ?s22) ?s32
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · intro a n h; simp [Outside] at h ⊢; omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem sqrt_big3 :
    Summary Fv256.SqrtProg.program Fv256.Amd64.SqrtLib.sqrtEntry
      (fun s => SPre s ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0)
      SPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, hxj⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧
        s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs40 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hor : ¬ (s.mem.readLE ((s.regs 3).toNat + 8) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0) := by
    rintro ⟨a, b, c⟩; omega
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, hor, hxj] until [Fv256.Amd64.SqrtLib.sqrtEntry + 0x205]
    calls [Fv256.CodeIn.lib_summary hcLsh (Fv256.Amd64.LshSumA.lsh_summary_alias (s.regs 4 - 40#64)),
           Fv256.CodeIn.lib_summary hcRsh (Fv256.Amd64.RshSum.rsh_summary (s.regs 4 - 72#64) (s.regs 3))]
  all_goals grab_const Fv256.Spec.lsh as hLv
  all_goals grab_const Fv256.Spec.rsh as hRv
  all_goals grab_frame 40 as hLf
  all_goals grab_frame 72 as hRf
  all_goals have hxb : s.mem.readLE ((s.regs 3).toNat + 8) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  all_goals (simp only [valueAt, Util.readLE_32] at hLv hRv)
  all_goals (simp only [hs40, hs72] at hLv hRv)
  all_goals (simp (disch := omega) only [valueAt, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside] at hLv hRv)
  have hl0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hl1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hl2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hl3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  obtain ⟨k, hk⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 3).toNat + 24) 8) = k := ⟨_, rfl⟩
  have hbl := Fv256.B.f64_bl3 (s.mem.readLE (s.regs 3).toNat 8) (s.mem.readLE ((s.regs 3).toNat + 8) 8) (s.mem.readLE ((s.regs 3).toNat + 16) 8) (s.mem.readLE ((s.regs 3).toNat + 24) 8) k hl0 hl1 hl2 hl3 hxj hk
  have hkj : k < 64 := by have := Util.clz_bl 64 (s.mem.readLE ((s.regs 3).toNat + 24) 8) hl3; have := SqrtHead.bl_pos _ hxj; omega
  rw [hk] at hLv hRv
  have hcl : ((BitVec.ofNat 64 (63 - k) + 194#64) >>> 1).toNat = (63 - k + 194) / 2 := SqrtHead.shr1_add (63 - k) 194 (by omega)
  rw [hcl] at hLv hRv
  have harith := SqrtHead.head_arith _ (256 - k) ((63 - k + 194) / 2) hbl (by omega) (by omega) (by omega)
  obtain ⟨hc1, hc128, hXinv, hX64, hX256⟩ := harith
  simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, show (256 : Nat) ^ 8 = 2 ^ 64 by decide,
    Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)] at hLv
  have hlsh : Spec.lsh 1 ((63 - k + 194) / 2) = 2 ^ ((63 - k + 194) / 2) := by
    unfold Spec.lsh
    try unfold Spec.W
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hc128) (by decide))
  rw [hlsh] at hLv
  simp (disch := (simp [Outside]; omega)) only [hLf.readLE] at hRv
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_inside] at hRv
  have hsumA : s'.mem.readLE ((s.regs 4).toNat - 40) 8 + 2 ^ 64 * s'.mem.readLE ((s.regs 4).toNat - 40 + 8) 8 +
      2 ^ 128 * s'.mem.readLE ((s.regs 4).toNat - 40 + 16) 8 + 2 ^ 192 * s'.mem.readLE ((s.regs 4).toNat - 40 + 24) 8 = 2 ^ ((63 - k + 194) / 2) := by
    rw [hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega),
      hRf.readLE _ _ (by simp [Outside]; omega), hRf.readLE _ _ (by simp [Outside]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hLv
  have hXeq : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 18446744073709551616 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have hr0 : s'.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 64 := Util.readLE8_lt _ _
  grab_proj_of hRf regs 4 as hs4
  grab_proj_of hRf regs 5 as hs5
  grab_proj_of hRf regs 14 as hs14
  grab_proj_of hRf xmm 15 as hsx
  grab_proj_of hLf regs 14 as hl14
  grab_proj_of hLf regs 5 as hl5
  grab_proj_of hLf xmm 15 as hlx
  have hXs : s.mem.readLE (s.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 8 + 2 ^ 64 * s.mem.readLE ((s.regs 3).toNat + 8) 8 + 2 ^ 128 * s.mem.readLE ((s.regs 3).toNat + 16) 8 + 2 ^ 192 * s.mem.readLE ((s.regs 3).toNat + 24) 8 := by
    rw [Util.readLE_32]
  have f1 : (s.regs 4).toNat - 72 + 8 = (s.regs 4).toNat - 64 := by omega
  have f2 : (s.regs 4).toNat - 72 + 16 = (s.regs 4).toNat - 56 := by omega
  have f3 : (s.regs 4).toNat - 72 + 24 = (s.regs 4).toNat - 48 := by omega
  have g1 : (s.regs 4).toNat - 40 + 8 = (s.regs 4).toNat - 32 := by omega
  have g2 : (s.regs 4).toNat - 40 + 16 = (s.regs 4).toNat - 24 := by omega
  have g3 : (s.regs 4).toNat - 40 + 24 = (s.regs 4).toNat - 16 := by omega
  simp only [f1, f2, f3, ← hXs, Spec.rsh] at hRv
  simp only [g1, g2, g3] at hsumA
  refine big_loop s (s.mem.readLE (s.regs 3).toNat 32) (s.regs 0) (s.regs 3) (SPost s) (by omega) (by omega) hra2 hdz hdx hdg hgb hnw2 hgr hsp (by omega)
    (fun r S' hsq h0 h4 h5 h14 hx15' hdf hmx hr hfr => ⟨h0, h4, h5, h14, by rw [hx15', hx15], hdf, hmx, by rw [hr]; exact hsq, hfr⟩)
    (2 ^ ((63 - k + 194) / 2)) (s'.mem.readLE ((s.regs 4).toNat - 40) 8) (s'.mem.readLE ((s.regs 4).toNat - 32) 8) (s'.mem.readLE ((s.regs 4).toNat - 24) 8) (s'.mem.readLE ((s.regs 4).toNat - 16) 8)
    (s'.mem.readLE ((s.regs 4).toNat - 72) 8) (s'.mem.readLE ((s.regs 4).toNat - 64) 8) (s'.mem.readLE ((s.regs 4).toNat - 56) 8) (s'.mem.readLE ((s.regs 4).toNat - 48) 8)
    _ hsumA.symm ?inv hRv (Nat.two_pow_pos _) (Nat.pow_le_pow_right (by omega) hc128) (by rw [hXeq];  exact hXinv) ?hXm
  case hXm =>
    rw [Util.readLE_32]
    simp (disch := (simp [Outside]; omega)) only [hRf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    simp (disch := (simp [Outside]; omega)) only [hLf.readLE]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Janus.Arm64.Memory.readLE_writeLE_inside]
    exact hXs.symm
  case inv =>
    refine ⟨?rip, ?r4, ?r5, ?r14, ?x15, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?mret, ?msav, ?mz, ?mx,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _,
      Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, Util.readLE8_lt _ _, ?hwin, ?hxacc, ?hzacc, hzw, hxw, ?hfrm⟩
    case rip => show (4957573#64 : BitVec 64) = BitVec.ofNat 64 headB; decide
    case r4 => rw [hs4]; simp [setRegF, sub144]
    case r5 => rw [hs5]; simp [setRegF, hl5]
    case r14 => rw [hs14]; simp [setRegF, hl14]
    case x15 => rw [hsx]; simp [hlx, hx15]
    case mret => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]
    case msav => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 5); omega
    case mz => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 0); omega
    case mx => simp (disch := (simp [Outside]; omega)) only [hRf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; simp (disch := (simp [Outside]; omega)) only [hLf.readLE]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside]; have hb := BitVec.isLt (s.regs 3); omega
    case hwin => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hacc
    case hxacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hx
    case hzacc => rw [hRf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [hLf.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hz
    case hfrm =>
      refine MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)])
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?A3 hLf ?s13)
        (MemFrame.trans (rs := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) (rs'' := [((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18)]) ?B3 hRf ?s23) ?s33
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x1f0, (s.regs 4).toNat + 0x18), List.mem_cons_self .., by omega, by omega⟩)
      · intro a n h; simp [Outside] at h ⊢; omega
      · intro a n h; simp [Outside] at h ⊢; omega

/-- the 256-bit path: some upper limb of `x` is non-zero -/
theorem sqrt_big :
    Summary Fv256.SqrtProg.program Fv256.Amd64.SqrtLib.sqrtEntry
      (fun s => SPre s ∧ (s.mem.readLE ((s.regs 3).toNat + 8) 8 ≠ 0 ∨ s.mem.readLE ((s.regs 3).toNat + 16) 8 ≠ 0 ∨
        s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0))
      SPost := by
  intro s hpc ⟨hpre, hb⟩
  by_cases h3 : s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE ((s.regs 3).toNat + 16) 8 = 0
    · exact sqrt_big1 s hpc ⟨hpre, h2, h3, by omega⟩
    · exact sqrt_big2 s hpc ⟨hpre, h3, h2⟩
  · exact sqrt_big3 s hpc ⟨hpre, h3⟩

end Fv256.Amd64.SqrtLib
