import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL
import Fv256.Amd64.UdivremM
import Fv256.CodeIn

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.DivModB

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- The part of `DivMod` after the (possible) un-aliasing allocation: from the merge point (`+0x8c`) with `m'` in `RDI`. -/
theorem partB (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (z x y m : BitVec 64) (m' : Nat) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret) (s st : State)
    (hg : StackGuardOK s 0x198) (hlow : 4256 ≤ (s.regs 4).toNat) (hnw : (s.regs 4).toNat + 0x28 ≤ 2 ^ 48)
    (hacc : s.mem.accessible ((s.regs 4).toNat - 4256) (4256 + 0x28) true = true)
    (hout : Outside ((s.regs 4).toNat - 4256) (4256 + 0x28) rt)
    (hzw : z.toNat + 32 ≤ 2 ^ 48) (hz : s.mem.accessible z.toNat 32 true = true)
    (hxw : x.toNat + 32 ≤ 2 ^ 48) (hx : s.mem.accessible x.toNat 32 false = true)
    (hyw : y.toNat + 32 ≤ 2 ^ 48) (hy : s.mem.accessible y.toNat 32 false = true)
    (hmw : m' + 32 ≤ 2 ^ 48) (hm : s.mem.accessible m' 32 true = true)
    (hxo : Outside x.toNat 32 rt) (hyo : Outside y.toNat 32 rt) (hzo : Outside z.toNat 32 rt)
    (hdz : z.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ z.toNat)
    (hdx : x.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ x.toNat)
    (hdy : y.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ y.toNat)
    (hdm : m' + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ m')
    (hzm : z.toNat + 32 ≤ m' ∨ m' + 32 ≤ z.toNat)
    (hdg : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16)
    (hgo : Outside ((s.regs 14).toNat + 16) 8 rt)
    (hm' : (z ≠ m → m' = m.toNat) ∧ (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s.mem.accessible m' 32 true = true))
    (hm'r : InRanges m' 32 rt ∨ m' = m.toNat)
    (hrip : st.rip = BitVec.ofNat 64 (Extracted.entry + 0x8c))
    (h0 : st.regs 0 = z) (h3 : st.regs 3 = x) (h1 : st.regs 1 = y) (h7 : (st.regs 7).toNat = m')
    (h4 : st.regs 4 = s.regs 4 - 0x98#64) (h5 : st.regs 5 = s.regs 4 - 8#64) (h14 : st.regs 14 = s.regs 14)
    (hx15 : st.xmm 15 = 0) (hdf : st.df = false) (hsx15 : s.xmm 15 = 0)
    (hfr : MemFrame s.mem st.mem (rt ++ [((s.regs 4).toNat - 4256, (s.regs 4).toNat + 0x28)]))
    (hspill : st.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat)
    (hretslot : st.mem.readLE (s.regs 4).toNat 8 = ret)
    (hbp : st.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    Reaches ((Extracted.program.link impl).withExit ret) st
      (IsReturn fun s' =>
        ABIReturn s s' ∧ s'.regs 0 = z ∧
          ∃ m'', (s'.regs 3).toNat = m'' ∧ (z ≠ m → m'' = m.toNat) ∧
            (z = m → InRanges m'' 32 rt ∧ m'' % 16 = 0 ∧ s'.mem.accessible m'' 32 true = true) ∧
            valueAt s' z 32 = Fv256.B.divSpec (valueAt s x 32) (valueAt s y 32) ∧
            s'.mem.readLE m'' 32 = Fv256.B.modSpec (valueAt s x 32) (valueAt s y 32) ∧
            MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
              ((s.regs 4).toNat - 4256, (s.regs 4).toNat + 0x28)])) := by
  have e8 : BitVec.toNat (s.regs 4) - 48 = BitVec.toNat (s.regs 4) - 56 + 8 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have e16 : BitVec.toNat (s.regs 4) - 40 = BitVec.toNat (s.regs 4) - 56 + 16 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have e24 : BitVec.toNat (s.regs 4) - 32 = BitVec.toNat (s.regs 4) - 56 + 24 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have f8 : BitVec.toNat (s.regs 4) - 80 = BitVec.toNat (s.regs 4) - 88 + 8 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have f16 : BitVec.toNat (s.regs 4) - 72 = BitVec.toNat (s.regs 4) - 88 + 16 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have f24 : BitVec.toNat (s.regs 4) - 64 = BitVec.toNat (s.regs 4) - 88 + 24 := Fv256.B.sub_off _ _ _ _ (Nat.le_trans (by decide) hlow) rfl
  have h7' : st.regs 7 = BitVec.ofNat 64 m' := by rw [← h7]; simp
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hgo
  simp only [valueAt]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hy0 := Util.readLE8_lt s.mem y.toNat
  have hy1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have hy2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have hy3 := Util.readLE8_lt s.mem (y.toNat + 24)
  have hdv := Nat.div_le_self (s.mem.readLE x.toNat 8) (s.mem.readLE y.toNat 8)
  janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary_link impl hcChain Fv256.Amd64.UdivremM.udivrem_rem_s]
  all_goals (try clear hdx hdy hdg hgo hxo hyo)
  all_goals (first | refine ⟨?_, m', rfl, hm'.1, hm'.2, ?_, ?_, ?_⟩ | refine ⟨m', rfl, hm'.1, hm'.2, ?_, ?_, ?_⟩)
  all_goals (first
    | (rcases hm'r with hr | hr
       · janus_frame
       · subst hr; janus_frame)
    | skip)
  all_goals (first | (simp [hsx15]; done) | skip)
  all_goals (try rw [e8, e16, e24])
  all_goals (try rw [f8, f16, f24])
  all_goals (
    try set_option maxHeartbeats 300000 in simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_div, Nat.zero_mod, Nat.reducePow, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right, Fv256.B.modSpec_zero_left, Fv256.B.modSpec_zero_right, Util.readLE8_mod])
  all_goals (try clear hdz hdx hdy hdm hzm hdg hgo hout hxo hyo hzo hm' hm'r hacc hlow hnw hnw2 hgl hgb hgr hzw hz hxw hx hyw hy hmw hm hfr hrip h0 h3 h1 h7 h7' h4 h5 h14 e8 e16 e24 f8 f16 f24)
  all_goals (
    first
    | with_reducible assumption
    | (rw [Fv256.B.divSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | (with_reducible exact Fv256.B.one_eq_div _ _ (by omega) (by omega))
           | exact Fv256.B.one_eq_div _ _ (by omega) (by omega)
           | (with_reducible exact (Nat.div_eq_of_lt (by omega)).symm)
           | exact (Nat.div_eq_of_lt (by omega)).symm
           | (with_reducible exact Fv256.B.div_congr _ _ _ (by omega))
           | exact Fv256.B.div_congr _ _ _ (by omega)))
    | (rw [Fv256.B.modSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | (rw [Fv256.B.mod64_mod _ _ (by omega)]; with_reducible exact Fv256.B.mod_congr _ _ _ (by omega))
           | (with_reducible exact Fv256.B.zero_eq_mod_self _ _ (by omega))
           | exact Fv256.B.zero_eq_mod_self _ _ (by omega)
           | (with_reducible exact (Nat.mod_eq_of_lt (by omega)).symm)
           | exact (Nat.mod_eq_of_lt (by omega)).symm
           | (with_reducible exact Fv256.B.mod_congr _ _ _ (by omega))
           | exact Fv256.B.mod_congr _ _ _ (by omega)
           | (rw [Fv256.B.mod64_mod _ _ (by omega)]; exact Fv256.B.mod_congr _ _ _ (by omega))))
    | (exfalso; omega))


end Fv256.Amd64.DivModB
