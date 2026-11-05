import Fv256.Arm64.ChainProg
import Fv256.Arm64.ModProg
import Fv256.Arm64.CodeIn
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Arm64.UdivremFront
import Fv256.Arm64.UdivremA
import Fv256.Arm64.UdivremD
import Fv256.Arm64.UdivremE
import Fv256.Arm64.UdivremF
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.DivLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremD

namespace Fv256.Arm64.ModSum

set_option maxRecDepth 200000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Fv256.Arm64.ModProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev modEntry : Nat := segAddr Fv256.Arm64.ModProg.program "github.com/holiman/uint256.(*Int).Mod"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem mod_summary :
    Summary Fv256.Arm64.ModProg.program modEntry
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 448 ∧ StackOK s 488 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 488 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat))
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.modSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 488, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 16)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hgw, hzb, hza, hxb, hxa, hyb, hya, hdz, hdx, hdy⟩
  have hx0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 2).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 2).toNat + 24)
  janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] until [modEntry + 0x98, modEntry + 0xf0] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcLib (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 4) (by decide) (by decide))]
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Fv256.Arm64.DivLemmas.chain_zero_iff _ _ _ _ _ _ _ _ hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3] at *)
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · exact Fv256.Arm64.DivLemmas.mclose_zero _
    · exact Fv256.Arm64.DivLemmas.mod_early_frame _ _ _ _ _ _ _ _ _ _ _ _ _ hsb (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · exact Fv256.Arm64.DivLemmas.mclose_eq _ _ _ _ _ _ _ _ (by janus_assumption) (by janus_assumption)
    · exact Fv256.Arm64.DivLemmas.mod_early_frame _ _ _ _ _ _ _ _ _ _ _ _ _ hsb (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  · have hy0n : s.mem.readLE (s.regs 2).toNat 8 ≠ 0 := by omega
    janus_run [Util.readLE_32, Nat.or_eq_zero_iff, Fv256.B.wv4_eq, Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
    trace_state
    sorry
  · rename_i hr hq hf
    trace_state
    sorry
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      repeat' rw [if_neg (by omega)]
    · exact Fv256.Arm64.DivLemmas.mclose_lt _ _ (by janus_assumption) (by janus_assumption)
    · exact Fv256.Arm64.DivLemmas.mod_early_frame _ _ _ _ _ _ _ _ _ _ _ _ _ hsb (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

end Fv256.Arm64.ModSum
