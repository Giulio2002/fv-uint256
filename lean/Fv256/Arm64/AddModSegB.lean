import Extracted
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
import Fv256.UtilAM
import Fv256.Amd64.AddModTac
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModSegB

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev PreS (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 816 ∧
    s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧
    Extracted.program.DataLoaded s.mem ∧
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

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segB (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1c0))
    (hm : ¬ (S.mem.readLE (S.regs 3).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 3).toNat + 24) 8 = 0))
    (hne : S.regs 3 ≠ S.regs 0)
    (hmb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hr8 : S.regs 8 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 3).toNat + 24) 8)) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x214)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x214) ∧ S'.mem = S.mem ∧ S'.sp = S.sp ∧ S'.regs 8 = S.regs 3 ∧
        (∀ i, i ≠ 8 → i ≠ 9 → i ≠ 10 → S'.regs i = S.regs i)) := by
  janus_run [Nat.or_eq_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, BitVec.toNat_ofNat] until [Extracted.entry + 0x214]
  exact Janus.Tactic.ReachesRet.done (by simp [Extracted.entry, setReg]) ⟨by simp [Extracted.entry, setReg], rfl, rfl, by simp [setReg],
    fun i h8 h9 h10 => by simp [setReg, h8, h9, h10]⟩

set_option hygiene false in
macro "segC_close" : tactic => `(tactic| (
  first
  | (-- no-overflow stop
     apply Janus.Tactic.ReachesRet.done
     · simp [Extracted.entry]
       done
     refine ⟨by simp [Extracted.entry], rfl, fun i h9 h10 => by simp [setReg, h9, h10], ?_, ?_⟩
     · dsimp only
       janus_frame
     · dsimp only
       simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
       (try simp only [Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Util.readLE8_mod, Bool.toNat_false, e1n, e2n] at *)
       (try simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *)
       (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *)
       clear_env_facts
       janus_carry_nf at *
       janus_omega_values)
  | (-- overflow stop: contradiction with hnov
     exfalso
     (try simp only [e1n, e2n] at hnov)
     (try simp only [Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Util.readLE8_mod, Bool.toNat_false, e1n, e2n] at *)
     (try simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *)
     (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *)
     clear_env_facts
     janus_carry_nf at *
     janus_omega_values)))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segC (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x214))
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hxb : (S.regs 1).toNat + 32 ≤ 2 ^ 48) (hxa : S.mem.accessible (S.regs 1).toNat 32 false = true)
    (hyb : (S.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : S.mem.accessible (S.regs 2).toNat 32 false = true)
    (hzx : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 2 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 2).toNat ∨ (S.regs 2).toNat + 32 ≤ (S.regs 0).toNat)
    (hnov : S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32 < 2 ^ 256) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x318)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x318) ∧ S'.sp = S.sp ∧
        (∀ i, i ≠ 9 → i ≠ 10 → S'.regs i = S.regs i) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32)] ∧
        S'.mem.readLE (S.regs 0).toNat 32 = S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32) := by
  have bx0 := Util.readLE8_lt S.mem (S.regs 1).toNat
  have bx1 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 8)
  have bx2 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 16)
  have bx3 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 24)
  have by0 := Util.readLE8_lt S.mem (S.regs 2).toNat
  have by1 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 8)
  have by2 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 16)
  have by3 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 24)
  by_cases e1 : S.regs 0 = S.regs 1 <;> by_cases e2 : S.regs 0 = S.regs 2
  · have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    janus_run [Util.readLE_32, e1n, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segC_close
  · have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 2).toNat = (S.regs 2).toNat := rfl
    janus_run [Util.readLE_32, e1n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segC_close
  · have hzx' := hzx.resolve_left e1
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    have e1n : (S.regs 1).toNat = (S.regs 1).toNat := rfl
    janus_run [Util.readLE_32, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segC_close
  · have hzx' := hzx.resolve_left e1
    have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 1).toNat = (S.regs 1).toNat := rfl
    have e2n : (S.regs 2).toNat = (S.regs 2).toNat := rfl
    janus_run [Util.readLE_32] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segC_close

set_option hygiene false in
macro "segCov_close" : tactic => `(tactic| (
  first
  | (-- no-overflow stop
     apply Janus.Tactic.ReachesRet.done
     · simp [Extracted.entry]
       done
     refine ⟨by simp [Extracted.entry], rfl, fun i h9 h10 => by simp [setReg, h9, h10], ?_, ?_⟩
     · dsimp only
       janus_frame
     · dsimp only
       simp (disch := omega) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
       (try simp only [Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Util.readLE8_mod, Bool.toNat_false, e1n, e2n] at *)
       (try simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *)
       (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *)
       clear_env_facts
       janus_carry_nf at *
       janus_omega_values)
  | (-- overflow stop: contradiction with hov
     exfalso
     (try simp only [e1n, e2n] at hov)
     (try simp only [Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Util.readLE8_mod, Bool.toNat_false, e1n, e2n] at *)
     (try simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *)
     (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *)
     clear_env_facts
     janus_carry_nf at *
     janus_omega_values)))


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segCov (S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x214))
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hxb : (S.regs 1).toNat + 32 ≤ 2 ^ 48) (hxa : S.mem.accessible (S.regs 1).toNat 32 false = true)
    (hyb : (S.regs 2).toNat + 32 ≤ 2 ^ 48) (hya : S.mem.accessible (S.regs 2).toNat 32 false = true)
    (hzx : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 2 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 2).toNat ∨ (S.regs 2).toNat + 32 ≤ (S.regs 0).toNat)
    (hov : 2 ^ 256 ≤ S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32) :
    Janus.Tactic.ReachesRet Extracted.program (BitVec.ofNat 64 (Extracted.entry + 0x25c)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x25c) ∧ S'.sp = S.sp ∧
        (∀ i, i ≠ 9 → i ≠ 10 → S'.regs i = S.regs i) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32)] ∧
        S'.mem.readLE (S.regs 0).toNat 32 + 2 ^ 256 = S.mem.readLE (S.regs 1).toNat 32 + S.mem.readLE (S.regs 2).toNat 32) := by
  have bx0 := Util.readLE8_lt S.mem (S.regs 1).toNat
  have bx1 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 8)
  have bx2 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 16)
  have bx3 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 24)
  have by0 := Util.readLE8_lt S.mem (S.regs 2).toNat
  have by1 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 8)
  have by2 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 16)
  have by3 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 24)
  by_cases e1 : S.regs 0 = S.regs 1 <;> by_cases e2 : S.regs 0 = S.regs 2
  · have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    janus_run [Util.readLE_32, e1n, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segCov_close
  · have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 2).toNat = (S.regs 2).toNat := rfl
    janus_run [Util.readLE_32, e1n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segCov_close
  · have hzx' := hzx.resolve_left e1
    have e2n : (S.regs 2).toNat = (S.regs 0).toNat := by rw [← e2]
    have e1n : (S.regs 1).toNat = (S.regs 1).toNat := rfl
    janus_run [Util.readLE_32, e2n] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segCov_close
  · have hzx' := hzx.resolve_left e1
    have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 1).toNat = (S.regs 1).toNat := rfl
    have e2n : (S.regs 2).toNat = (S.regs 2).toNat := rfl
    janus_run [Util.readLE_32] until [Extracted.entry + 0x318, Extracted.entry + 0x25c]
    all_goals segCov_close

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segD (S : State) (R : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x318))
    (hsal : S.sp.toNat % 16 = 0) (hsb : 488 ≤ S.sp.toNat) (hsc : S.sp.toNat + 16 ≤ 2 ^ 48)
    (hsw : S.mem.accessible (S.sp.toNat - 488) 504 true = true)
    (hg1 : (S.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible ((S.regs 28).toNat + 16) 8 false = true)
    (hg3 : S.mem.readLE ((S.regs 28).toNat + 16) 8 + 448 < S.sp.toNat)
    (hgw : (S.regs 28).toNat + 24 ≤ S.sp.toNat - 488 ∨ S.sp.toNat + 16 ≤ (S.regs 28).toNat + 16)
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hmb : (S.regs 8).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 8).toNat 32 false = true)
    (hdz : (S.regs 0).toNat + 32 ≤ S.sp.toNat - 488 ∨ S.sp.toNat + 16 ≤ (S.regs 0).toNat)
    (hdm : (S.regs 8).toNat + 32 ≤ S.sp.toNat - 488 ∨ S.sp.toNat + 16 ≤ (S.regs 8).toNat)
    (hret : S.mem.readLE S.sp.toNat 8 = R.toNat) (hRa : R.toNat % 4 = 0) (hRb : R.toNat < 2 ^ 56) :
    Janus.Tactic.ReachesRet Extracted.program R S
      (fun S' => S'.pc = R ∧ S'.sp = S.sp + 368 ∧ S'.regs 0 = S.regs 0 ∧ S'.regs 28 = S.regs 28 ∧
        S'.mem.readLE (S.regs 0).toNat 32 = Fv256.B.modSpec (S.mem.readLE (S.regs 0).toNat 32) (S.mem.readLE (S.regs 8).toNat 32) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), (S.sp.toNat - 488, S.sp.toNat - 8),
          (S.sp.toNat + 8, S.sp.toNat + 16)]) := by
  have hzr := S.mem.accessible_read_of_write hza
  janus_run [hret] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcMod Fv256.Arm64.ModSum.mod_summary]
  rename_i hv hf _
  exact ⟨hv, hf⟩

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segEF (S : State) (R : BitVec 64) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x25c))
    (hsal : S.sp.toNat % 16 = 0) (hsb : 344 ≤ S.sp.toNat) (hsc : S.sp.toNat + 384 ≤ 2 ^ 48)
    (hsw : S.mem.accessible (S.sp.toNat - 344) 728 true = true)
    (hdata : Extracted.program.DataLoaded S.mem)
    (hg1 : (S.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible ((S.regs 28).toNat + 16) 8 false = true)
    (hg3 : S.mem.readLE ((S.regs 28).toNat + 16) 8 + 304 < S.sp.toNat)
    (hgw : (S.regs 28).toNat + 24 ≤ S.sp.toNat - 344 ∨ S.sp.toNat + 384 ≤ (S.regs 28).toNat + 16)
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hmb : (S.regs 8).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 8).toNat 32 false = true)
    (hdz : (S.regs 0).toNat + 32 ≤ S.sp.toNat - 344 ∨ S.sp.toNat + 384 ≤ (S.regs 0).toNat)
    (hdm : (S.regs 8).toNat + 32 ≤ S.sp.toNat - 344 ∨ (S.regs 8).toNat = S.sp.toNat + 328 ∨ S.sp.toNat + 384 ≤ (S.regs 8).toNat)
    (hdmz : (S.regs 8).toNat + 32 ≤ (S.regs 0).toNat ∨ (S.regs 0).toNat + 32 ≤ (S.regs 8).toNat)
    (hm : ¬ (S.mem.readLE (S.regs 8).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 8).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 8).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 8).toNat + 24) 8 = 0))
    (hret : S.mem.readLE S.sp.toNat 8 = R.toNat) (hRa : R.toNat % 4 = 0) (hRb : R.toNat < 2 ^ 56) :
    Janus.Tactic.ReachesRet Extracted.program R S
      (fun S' => S'.pc = R ∧ S'.sp = S.sp + 368 ∧ S'.regs 0 = S.regs 0 ∧ S'.regs 28 = S.regs 28 ∧
        S'.mem.readLE (S.regs 0).toNat 32 = (S.mem.readLE (S.regs 0).toNat 32 + 2 ^ 256) % S.mem.readLE (S.regs 8).toNat 32 ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), (S.sp.toNat - 344, S.sp.toNat + 384)]) := by
  janus_data hdata [hsw, hza]
  janus_run [hret, Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv_writeLE_outside, Fv256.B.wv4_eq, Fv256.F.wv_zero5w, Fv256.F.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] until [Extracted.entry + 0x2f8] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 5) (by decide) (by decide))]
  rename_i hregs hq hrem hf
  have hz8 : s'.mem.readLE (S.sp.toNat + 376) 8 = (S.regs 0).toNat := by
    rw [hf.readLE _ _ (by simp only [Outside, and_true, setReg, reduceIte, Nat.reduceEqDiff, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (S.regs 0).isLt; simpa using this)
  have hret' : s'.mem.readLE S.sp.toNat 8 = R.toNat := by
    rw [hf.readLE _ _ (by simp only [Outside, and_true, setReg, reduceIte, Nat.reduceEqDiff, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hret
  janus_run [hz8, hret', Util.readLE_32]
  have e216 : (S.sp + 216#64).toNat = S.sp.toNat + 216 := by simp [BitVec.toNat_add]; omega
  have e248 : (S.sp + 248#64).toNat = S.sp.toNat + 248 := by simp [BitVec.toNat_add]; omega
  have e144 : (S.sp + 144#64).toNat = S.sp.toNat + 144 := by simp [BitVec.toNat_add]; omega
  simp only [setReg, reduceIte, Nat.reduceEqDiff, e216, e248, e144] at hf hrem
  refine ⟨?_, ?_⟩
  · simp (disch := omega) only [Fv256.B.wv_succ, Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] at hrem
    simp only [Nat.reducePow, Util.readLE8_mod, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.one_mod] at hrem
    exact Fv256.AM.eq_mod_congr _ _ _ _ _ _ (by omega) (by omega) (by omega) hrem
  · janus_frame

end Fv256.Arm64.AddModSegB
