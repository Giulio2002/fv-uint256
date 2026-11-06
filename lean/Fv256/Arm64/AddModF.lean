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
import Fv256.Amd64.AddModTac
import Fv256.UtilAM
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.AddModF

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
theorem addmod_fast : Summary Extracted.program Extracted.entry (fun s => PreS s ∧ (s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8 ∧ s.mem.readLE ((s.regs 2).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 3).toNat + 24) 8))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32)
          (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat + 16)]) := by
  intro s hpc ⟨⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, hsal, hsb, hsc, hsw, hdata, hgw, hzb, hza, hxb, hxa, hyb, hya, hmb, hma, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hgz⟩, hm3, hx3, hy3⟩
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
  janus_data hdata [hsw, hza]
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div, Fv256.B.wv_writeLE_outside, Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcMod Fv256.Arm64.ModSum.mod_summary, Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 5) (by decide) (by decide))]
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.reducePow, Util.readLE8_mod, BitVec.toNat_add, Fv256.AM.awc_fst, Fv256.AM.awc_c] at *)
  all_goals (try simp (disch := omega) only [Fv256.AM.dec_le_div, Fv256.AM.awc_fst, Fv256.AM.awc_c, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow] at *)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (
    (try simp only [Bool.toNat_false] at *)
    simp (disch := exact Bool.toNat_le _) only [Fv256.AM.ngc_flag, Fv256.AM.flag_mod] at *
    simp (disch := (clear * - bx0 bx1 bx2 bx3 by0 by1 by2 by3 bm0 bm1 bm2 bm3; decide_facts; omega)) only
      [Fv256.AM.dec_add_div, Fv256.AM.sbc_num, Fv256.AM.notsub, Fv256.AM.notflag] at *
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega)]
    refine (Fv256.AM.mod_cases4 _ _ _ ?_ ?_).symm <;> janus_carry_nf at * <;> janus_omega_values)

end Fv256.Arm64.AddModF
