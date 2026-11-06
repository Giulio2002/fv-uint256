import Fv256.Arm64.AddModProg
import Fv256.Arm64.SegCompose
import Fv256.Arm64.AddModEntry
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.UtilMDO
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.ModSum
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.ChainProg
import Fv256.Arm64.ModProg
import Fv256.Arm64.CodeIn
import Fv256.Amd64.AddModTac
import Fv256.UtilAM
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModF2

abbrev PreS (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 816 ∧
    s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧
    Fv256.Arm64.AddModProg.program.DataLoaded s.mem ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
    (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
    (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
    (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
    (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧
    ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
    ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
    ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat) ∧
    ((s.regs 3).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 3).toNat) ∧
    (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 1 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 2 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 2).toNat ∨ (s.regs 2).toNat + 32 ≤ (s.regs 0).toNat) ∧
    ((s.regs 28).toNat + 24 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 28).toNat + 16)

set_option hygiene false in
macro "af2_pipe" : tactic => `(tactic| (
  clear_env_facts
  (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, Util.readLE8_mod, BitVec.toNat_add, Fv256.AM.awc_fst, Fv256.AM.awc_c] at *)
  (try simp (disch := omega) only [Fv256.AM.dec_le_div, Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow] at *)
  (try simp only [Bool.toNat_false] at *)
  (try simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *)
  (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3 bm0 bm1 bm2 bm3; decide_facts; omega)) only
    [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *)
  all_goals (try simp only [Nat.mod_mod] at *)
  all_goals (janus_carry_nf at *; janus_omega_values)))

theorem mod_sub (x M : Nat) (h1 : M ≤ x) (h2 : x < 2 * M) : x % M = x - M := by
  rw [Nat.mod_eq_sub_mod h1]; exact Nat.mod_eq_of_lt (by omega)

set_option janus.nf.budget 400000 in
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem half1 (s : State) (hpc : s.pc = BitVec.ofNat 64 Fv256.Arm64.AddModProg.entry) (hpre : PreS s)
    (hm3 : s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0)
    (hx3 : s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8)
    (hy3 : s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8) :
    Janus.Tactic.ReachesRet Fv256.Arm64.AddModProg.program (BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x104)) s
      (fun S1 => S1.pc = BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x104) ∧ S1.sp = s.sp - 0x170#64 ∧
        S1.regs 0 = s.regs 0 ∧ S1.regs 3 = s.regs 3 ∧ S1.regs 18 = s.regs 18 ∧ S1.regs 28 = s.regs 28 ∧
        (S1.regs 1 = s.regs 1 ∨ S1.regs 1 = S1.sp + 112#64) ∧ (S1.regs 2 = s.regs 2 ∨ S1.regs 2 = S1.sp + 80#64) ∧
        S1.mem.readLE (S1.regs 1).toNat 32 = s.mem.readLE (s.regs 1).toNat 32 % s.mem.readLE (s.regs 3).toNat 32 ∧
        S1.mem.readLE (S1.regs 2).toNat 32 = s.mem.readLE (s.regs 2).toNat 32 % s.mem.readLE (s.regs 3).toNat 32 ∧
        S1.mem.readLE (s.sp.toNat - 0x170 - 8) 8 = (s.regs 29).toNat ∧ S1.mem.readLE (s.sp.toNat - 0x170) 8 = (s.regs 30).toNat ∧
        MemFrame s.mem S1.mem [(s.sp.toNat - 0x170 - 8, s.sp.toNat - 0x170 + 8), (s.sp.toNat - 0x170 + 80, s.sp.toNat - 0x170 + 144),
          (s.sp.toNat - 0x170 + 184, s.sp.toNat - 0x170 + 216)]) := by
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  have bx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have bx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have bx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have bx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have by0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have by1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have by2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have by3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  have bm0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have bm1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have bm2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have bm3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  have hx2 := show s.mem.readLE (s.regs 1).toNat 32 < 2 * s.mem.readLE (s.regs 3).toNat 32 by
    rw [Util.readLE_32, Util.readLE_32]; omega
  have hy2 := show s.mem.readLE (s.regs 2).toNat 32 < 2 * s.mem.readLE (s.regs 3).toNat 32 by
    rw [Util.readLE_32, Util.readLE_32]; omega
  simp only [Util.readLE_32] at hx2 hy2
  have hp256 : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  have hp288 : (s.sp - 288#64).toNat = s.sp.toNat - 288 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  have q1 : s.sp.toNat - 256 + 8 - (s.sp.toNat - 248) = 0 := by omega
  have q2 : s.sp.toNat - 256 + 16 - (s.sp.toNat - 240) = 0 := by omega
  have q3 : s.sp.toNat - 256 + 24 - (s.sp.toNat - 232) = 0 := by omega
  have q4 : s.sp.toNat - 288 + 8 - (s.sp.toNat - 280) = 0 := by omega
  have q5 : s.sp.toNat - 288 + 16 - (s.sp.toNat - 272) = 0 := by omega
  have q6 : s.sp.toNat - 288 + 24 - (s.sp.toNat - 264) = 0 := by omega
  have q0 : s.sp.toNat - 256 - (s.sp.toNat - 256) = 0 := by omega
  have q0' : s.sp.toNat - 288 - (s.sp.toNat - 288) = 0 := by omega
  clear hzm hzx hzy hgz hdata
  janus_run [Util.readLE_32] until [Fv256.Arm64.AddModProg.entry + 0x104]
  all_goals (
    apply Janus.Tactic.ReachesRet.done
    · first | rfl | simp [Fv256.Arm64.AddModProg.entry]
    refine ⟨by simp [Fv256.Arm64.AddModProg.entry], by simp [setReg], by simp [setReg], by simp [setReg], by simp [setReg], by simp [setReg],
      (by first | (left; simp [setReg]; done) | (right; simp [setReg]; try bv_omega)), (by first | (left; simp [setReg]; done) | (right; simp [setReg]; try bv_omega)), ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only
      simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      simp (config := {maxSteps := 4000000}) (disch := (keep_only hsb hsc hdx hdy hdm hdz hsal; omega)) only [hp256, hp288, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_inside]
      simp only [q0, q0', q1, q2, q3, q4, q5, q6, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.one_mul]
      first
      | (refine Eq.trans ?_ (Nat.mod_eq_of_lt ?_).symm <;> af2_pipe)
      | (refine Eq.trans (Nat.eq_sub_of_add_eq ?_) (mod_sub _ _ ?_ hx2).symm <;> af2_pipe)
    · dsimp only
      simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      simp (config := {maxSteps := 4000000}) (disch := (keep_only hsb hsc hdx hdy hdm hdz hsal; omega)) only [hp256, hp288, Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_inside]
      simp only [q0, q0', q1, q2, q3, q4, q5, q6, Nat.pow_zero, Nat.div_one, Nat.reducePow, Nat.one_mul]
      first
      | (refine Eq.trans ?_ (Nat.mod_eq_of_lt ?_).symm <;> af2_pipe)
      | (refine Eq.trans (Nat.eq_sub_of_add_eq ?_) (mod_sub _ _ ?_ hy2).symm <;> af2_pipe)
    · dsimp only
      simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
        Janus.Arm64.Memory.readLE_writeLE_inside]
      have a0 : s.sp.toNat - 368 - 8 - (s.sp.toNat - 376) = 0 := by omega
      simp only [a0, Nat.pow_zero, Nat.div_one]
      have := (s.regs 29).isLt
      simp only [Nat.reducePow] at this ⊢
      exact Nat.mod_eq_of_lt this
    · dsimp only
      simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      have := h30b
      simp only [Nat.reducePow] at this ⊢
      exact Nat.mod_eq_of_lt (by omega)
    · dsimp only
      janus_frame)

-- second half of the fast path, from 0xba514: x1', x2' point at the reduced operands (both below m)
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem half2 (S : State) (hpc : S.pc = BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x104))
    (hret1 : S.mem.readLE S.sp.toNat 8 % 4 = 0) (hret2 : S.mem.readLE S.sp.toNat 8 < 2 ^ 56)
    (hsal : S.sp.toNat % 16 = 0) (hsb : 8 ≤ S.sp.toNat) (hsc : S.sp.toNat + 0x170 ≤ 2 ^ 48)
    (hsw : S.mem.accessible (S.sp.toNat - 8) 256 true = true)
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hxb : (S.regs 1).toNat + 32 ≤ 2 ^ 48) (hxa : S.mem.accessible (S.regs 1).toNat 32 false = true)
    (hyb : (S.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : S.mem.accessible (S.regs 2).toNat 32 false = true)
    (hmb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hdz : (S.regs 0).toNat + 32 ≤ S.sp.toNat - 8 ∨ S.sp.toNat + 248 ≤ (S.regs 0).toNat)
    (hdx : (S.regs 1).toNat + 32 ≤ S.sp.toNat + 184 ∨ S.sp.toNat + 216 ≤ (S.regs 1).toNat)
    (hdy : (S.regs 2).toNat + 32 ≤ S.sp.toNat + 184 ∨ S.sp.toNat + 216 ≤ (S.regs 2).toNat)
    (hdm : (S.regs 3).toNat + 32 ≤ S.sp.toNat + 184 ∨ S.sp.toNat + 216 ≤ (S.regs 3).toNat)
    (hx : S.mem.readLE (S.regs 1).toNat 32 < S.mem.readLE (S.regs 3).toNat 32)
    (hy : S.mem.readLE (S.regs 2).toNat 32 < S.mem.readLE (S.regs 3).toNat 32) :
    Janus.Tactic.ReachesRet Fv256.Arm64.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE S.sp.toNat 8)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (S.mem.readLE S.sp.toNat 8) ∧ S'.sp = S.sp + 0x170#64 ∧ S'.regs 0 = S.regs 0 ∧ S'.regs 18 = S.regs 18 ∧ S'.regs 28 = S.regs 28 ∧
        S'.regs 29 = BitVec.ofNat 64 (S.mem.readLE (S.sp.toNat - 8) 8) ∧ S'.regs 30 = BitVec.ofNat 64 (S.mem.readLE S.sp.toNat 8) ∧
        S'.mem.readLE (S.regs 0).toNat 32 = (S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32) % S.mem.readLE (S.regs 3).toNat 32 ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), (S.sp.toNat + 184, S.sp.toNat + 216)]) := by
  have bx0 := Util.readLE8_lt S.mem (S.regs 1).toNat
  have bx1 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 8)
  have bx2 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 16)
  have bx3 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 24)
  have by0 := Util.readLE8_lt S.mem (S.regs 2).toNat
  have by1 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 8)
  have by2 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 16)
  have by3 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 24)
  have bm0 := Util.readLE8_lt S.mem (S.regs 3).toNat
  have bm1 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 8)
  have bm2 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 16)
  have bm3 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 24)
  simp only [Util.readLE_32] at hx hy
  janus_run [Util.readLE_32]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals clear_env_facts
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, Util.readLE8_mod, BitVec.toNat_add, Fv256.AM.awc_fst, Fv256.AM.awc_c] at *)
  all_goals (try simp (disch := omega) only [Fv256.AM.dec_le_div, Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow] at *)
  all_goals (
    (try simp only [Bool.toNat_false] at *)
    simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *
    simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3 bm0 bm1 bm2 bm3; decide_facts; omega)) only
      [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *
    refine (Fv256.AM.mod_cases4 _ _ _ ?_ ?_).symm <;> janus_carry_nf at * <;> janus_omega_values)

open Fv256.Arm64.SegCompose (seg_trans seg_mono)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fast2 : Summary Fv256.Arm64.AddModProg.program Fv256.Arm64.AddModProg.entry
    (fun s => PreS s ∧ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧
      s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)]) := by
  intro s hpc ⟨hpre, hm3, hx3, hy3⟩
  have h1 := half1 s hpc hpre hm3 hx3 hy3
  obtain ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩ := hpre
  refine seg_trans h1 (fun S1 hpc1 hq1 => ?_)
  obtain ⟨-, hsp1, r0, r3, r18, r28, hx1, hy1, vx, vy, m29, m30, hfr⟩ := hq1
  have s1 : S1.sp.toNat = s.sp.toNat - 0x170 := by
    rw [hsp1, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  have hout : ∀ a n, (a + n ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ a) → S1.mem.readLE a n = s.mem.readLE a n :=
    fun a n h => hfr.readLE a n (by simp only [Janus.outside_cons, Janus.outside_nil, and_true]; omega)
  have hac := hfr.accessible
  have hMpos : 0 < s.mem.readLE (s.regs 3).toNat 32 := by
    rw [Util.readLE_32]; have := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24); omega
  have hmS : S1.mem.readLE (S1.regs 3).toNat 32 = s.mem.readLE (s.regs 3).toNat 32 := by
    rw [r3]; exact hout _ _ (by omega)
  have p1 : (S1.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ S1.mem.accessible (S1.regs 1).toNat 32 false = true ∧
      ((S1.regs 1).toNat + 32 ≤ S1.sp.toNat + 184 ∨ S1.sp.toNat + 216 ≤ (S1.regs 1).toNat) := by
    rcases hx1 with h | h
    · rw [h, hac]; exact ⟨hxb, hxa, by omega⟩
    · have e : (S1.regs 1).toNat = S1.sp.toNat + 112 := by
        rw [h, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := S1.sp.isLt; omega
      rw [e]
      refine ⟨by omega, ?_, by omega⟩
      rw [hac]; exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega))
  have p2 : (S1.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ S1.mem.accessible (S1.regs 2).toNat 32 false = true ∧
      ((S1.regs 2).toNat + 32 ≤ S1.sp.toNat + 184 ∨ S1.sp.toNat + 216 ≤ (S1.regs 2).toNat) := by
    rcases hy1 with h | h
    · rw [h, hac]; exact ⟨hyb, hya, by omega⟩
    · have e : (S1.regs 2).toNat = S1.sp.toNat + 80 := by
        rw [h, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := S1.sp.isLt; omega
      rw [e]
      refine ⟨by omega, ?_, by omega⟩
      rw [hac]; exact Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega))
  have m30n : S1.mem.readLE S1.sp.toNat 8 = (s.regs 30).toNat := by rw [s1]; exact m30
  have h2 := half2 S1 hpc1 (by rw [m30n]; exact h30a) (by rw [m30n]; exact h30b) (by omega) (by omega) (by omega)
    (by rw [hac, s1]; exact Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega))
    (by rw [r0]; exact hzb) (by rw [r0, hac]; exact hza) p1.1 p1.2.1 p2.1 p2.2.1
    (by rw [r3]; exact hmb) (by rw [r3, hac]; exact hma)
    (by rw [r0, s1]; omega) p1.2.2 p2.2.2 (by rw [r3, s1]; omega)
    (by rw [vx, hmS]; exact Nat.mod_lt _ hMpos) (by rw [vy, hmS]; exact Nat.mod_lt _ hMpos)
  have hret : BitVec.ofNat 64 (S1.mem.readLE S1.sp.toNat 8) = s.regs 30 := by
    rw [m30n]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (s.regs 30).isLt
  rw [hret] at h2
  refine seg_mono h2 ?_
  rintro S' ⟨q0, q1, q2, q3, q4, q5, q6, qv, qf⟩
  refine ⟨q0, ?_, by rw [q2, r0], by rw [q3, r18], by rw [q4, r28], ?_, q6, ?_, ?_⟩
  · rw [q1, hsp1]; bv_omega
  · rw [q5, s1, m29]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
  · rw [r0] at qv
    rw [qv, vx, vy, hmS]
    unfold Fv256.F.addmodSpec
    rw [if_neg (Nat.pos_iff_ne_zero.mp hMpos)]
    exact (Nat.add_mod _ _ _).symm
  · rw [r0] at qf
    refine hfr.trans qf ?_
    intro a n h
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    rw [s1] at *
    omega

end Fv256.Arm64.AddModF2
