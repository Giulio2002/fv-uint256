import Fv256.Arm64.DivModProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.UtilH
import Fv256.Arm64.ChainProg
import Fv256.Arm64.CodeIn
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.DivLemmas
import Fv256.Arm64.DivMLem
import Fv256.Arm64.DivMGlue

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.DivModLib

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Fv256.Arm64.DivModProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem outside_stk {a n : Nat} {rt : List (Nat × Nat)} {lo hi : Nat} (h1 : Outside a n rt) (h2 : a + n ≤ lo ∨ hi ≤ a) :
    Outside a n (rt ++ [(lo, hi)]) := by
  simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
  exact ⟨h1, h2⟩

theorem div64_goal (x y : Nat) (hx : x < 2 ^ 64) (hy : y ≠ 0) : x / y % 18446744073709551616 = Fv256.B.divSpec x y := by
  rw [Fv256.B.divSpec_of_ne _ _ hy]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by simpa using hx))

theorem mod64_goal (x y : Nat) (hx : x < 2 ^ 64) (hy : y ≠ 0) :
    (18446744073709551616 - x / y * y % 18446744073709551616 + x) % 18446744073709551616 =
    Fv256.B.modSpec x y := by
  rw [Fv256.B.modSpec_of_ne _ _ hy]
  have h3 : x / y * y ≤ x := Nat.div_mul_le_self _ _
  have h4 := Nat.mod_add_div x y
  have hx' : x < 18446744073709551616 := by simpa using hx
  rw [Nat.mod_eq_of_lt (by omega : x / y * y < 18446744073709551616)]
  have := Nat.mul_comm y (x / y)
  omega

abbrev dm : Nat := segAddr Fv256.Arm64.DivModProg.program "github.com/holiman/uint256.(*Int).DivMod"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- The code after the `udivrem` call (`+0x130`): copy the quotient to `z` and the remainder to `m'`, return. -/
theorem partC (rt : List (Nat × Nat)) (z m' : Nat) (ret : Nat) (Q R : Nat)
    (hret : RetAddr Fv256.Arm64.DivModProg.program ret) (s S : State)
    (hal : s.sp.toNat % 16 = 0) (hb : 4256 ≤ s.sp.toNat) (ha : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hdz : z + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ z)
    (hdm : m' + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ m')
    (hzm : z + 32 ≤ m' ∨ m' + 32 ≤ z)
    (hzb : z + 32 ≤ 2 ^ 48) (hmb : m' + 32 ≤ 2 ^ 48)
    (hpc : S.pc = BitVec.ofNat 64 (dm + 0x130)) (hsp : S.sp.toNat = s.sp.toNat - 160)
    (h18 : S.regs 18 = s.regs 18) (h28 : S.regs 28 = s.regs 28)
    (hfr : MemFrame s.mem S.mem (rt ++ [(s.sp.toNat - 4256, s.sp.toNat + 40)]))
    (hw : s.mem.accessible (s.sp.toNat - 4256) (4256 + 40) true = true)
    (hzw : s.mem.accessible z 32 true = true) (hmw : s.mem.accessible m' 32 true = true)
    (hretslot : S.mem.readLE S.sp.toNat 8 = ret)
    (hbp : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat)
    (hz8 : S.mem.readLE (S.sp.toNat + 168) 8 = z) (hm8 : S.mem.readLE (S.sp.toNat + 144) 8 = m')
    (hq : Fv256.B.wv S.mem (S.sp.toNat + 112) 4 = Q) (hr : Fv256.B.wv S.mem (S.sp.toNat + 80) 4 = R) :
    Reaches (Fv256.Arm64.DivModProg.program.withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ s'.regs 0 = BitVec.ofNat 64 z ∧
        (s'.regs 1).toNat = m' ∧ val256 s'.mem z = Q ∧ val256 s'.mem m' = R ∧
        MemFrame s.mem s'.mem (rt ++ [(z, z + 32), (m', m' + 32), (s.sp.toNat - 4256, s.sp.toNat + 40)])) := by
  have hret48 := hret.user
  have hspal : S.sp.toNat % 16 = 0 := by omega
  have hfa := hfr.accessible
  have hstk : S.mem.accessible (S.sp.toNat - 4096) 4296 true = true := by
    rw [hfa, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hstkr : S.mem.accessible (S.sp.toNat - 4096) 4296 false = true := Janus.Arm64.Memory.accessible_read_of_write _ hstk
  have hzb' : S.mem.accessible z 32 true = true := by rw [hfa]; exact hzw
  have hmb' : S.mem.accessible m' 32 true = true := by rw [hfa]; exact hmw
  simp only [dm, reduceSegAddr, Nat.reduceAdd] at hpc
  have hq' := hq
  have hr' := hr
  simp only [Fv256.B.wv4_eq] at hq' hr'
  rw [Util.readLE_32] at hq' hr'
  janus_run [Util.readLE_32, hretslot, hbp, hz8, hm8, hq', hr']
  simp only [Nat.add_assoc, Nat.reduceAdd] at hq' hr'
  refine ⟨?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := s.sp.isLt
    omega
  · have hf0 : MemFrame s.mem S.mem (rt ++ [(z, z + 32), (m', m' + 32), (s.sp.toNat - 4256, s.sp.toNat + 40)]) :=
      hfr.mono (by
        intro a n h
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
        exact ⟨h.1, h.2.2.2⟩)
    refine (((((((hf0.writeLE _ (r := (z, z + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (z, z + 32)) (by simp) (by omega) (by omega)).writeLE _
      (r := (z, z + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (z, z + 32)) (by simp) (by omega) (by omega)).writeLE _
      (r := (m', m' + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (m', m' + 32)) (by simp) (by omega) (by omega)).writeLE _
      (r := (m', m' + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (m', m' + 32)) (by simp) (by omega) (by omega)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
/-- The part of `DivMod` after the (possible) un-aliasing allocation: from the merge point (`+0x64`) with `m'` in `X3`. -/
theorem partB (rt : List (Nat × Nat)) (z x y m : BitVec 64) (m' : Nat) (ret : Nat)
    (hret : RetAddr Fv256.Arm64.DivModProg.program ret) (s st : State)
    (hal : s.sp.toNat % 16 = 0) (hb : 4256 ≤ s.sp.toNat) (ha : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 4256) (4256 + 40) true = true)
    (hout : Outside (s.sp.toNat - 4256) (4256 + 40) rt)
    (hzb : s.mem.accessible z.toNat 32 true = true) (hza : z.toNat + 32 ≤ 2 ^ 48)
    (hxb : s.mem.accessible x.toNat 32 false = true) (hxa : x.toNat + 32 ≤ 2 ^ 48)
    (hyb : s.mem.accessible y.toNat 32 false = true) (hya : y.toNat + 32 ≤ 2 ^ 48)
    (hmb : s.mem.accessible m'  32 true = true) (hma : m' + 32 ≤ 2 ^ 48)
    (hxo : Outside x.toNat 32 rt) (hyo : Outside y.toNat 32 rt) (hzo : Outside z.toNat 32 rt)
    (hdz : Apart z.toNat 32 (s.sp.toNat - 4256) (4256 + 40))
    (hdx : Apart x.toNat 32 (s.sp.toNat - 4256) (4256 + 40))
    (hdy : Apart y.toNat 32 (s.sp.toNat - 4256) (4256 + 40))
    (hdm : Apart m' 32 (s.sp.toNat - 4256) (4256 + 40))
    (hzm : Apart z.toNat 32 m' 32)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 464 < s.sp.toNat)
    (hdg : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4256) (4256 + 40))
    (hgo : Outside ((s.regs 28).toNat + 16) 8 rt)
    (hm'r : InRanges m' 32 rt ∨ m' = m.toNat)
    (hpc : st.pc = BitVec.ofNat 64 (dm + 0x64)) (hsp : st.sp.toNat = s.sp.toNat - 160)
    (h0 : st.regs 0 = z) (h1 : st.regs 1 = x) (h2 : st.regs 2 = y) (h3 : st.regs 3 = BitVec.ofNat 64 m')
    (h18 : st.regs 18 = s.regs 18) (h28 : st.regs 28 = s.regs 28) (h29 : st.regs 29 = s.sp - 168#64)
    (hfr : MemFrame s.mem st.mem (rt ++ [(s.sp.toNat - 4256, s.sp.toNat + 40)]))
    (hretslot : st.mem.readLE st.sp.toNat 8 = ret)
    (hbp : st.mem.readLE (st.sp.toNat - 8) 8 = (s.regs 29).toNat)
    (hz8 : st.mem.readLE (st.sp.toNat + 168) 8 = z.toNat)
    (hr30 : (s.regs 30).toNat % 4 = 0) (hr30b : (s.regs 30).toNat < 2 ^ 56) (hlr : s.regs 30 = BitVec.ofNat 64 ret) :
    Reaches (Fv256.Arm64.DivModProg.program.withExit ret) st
      (IsReturn fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        ∃ m'', (s'.regs 1).toNat = m'' ∧ m'' = m' ∧
          val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          val256 s'.mem m'' = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m', m' + 32), (s.sp.toNat - 4256, s.sp.toNat + 40)])) := by
  have hU := Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain
    (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 4) (by omega) (by omega))
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hy0 := Util.readLE8_lt s.mem y.toNat
  have hy1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have hy2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have hy3 := Util.readLE8_lt s.mem (y.toNat + 24)
  have hfa := hfr.accessible
  have h_lr := hlr
  have hxb' : st.mem.accessible x.toNat 32 false = true := by rw [hfa]; exact hxb
  have hyb' : st.mem.accessible y.toNat 32 false = true := by rw [hfa]; exact hyb
  have hzb' : st.mem.accessible z.toNat 32 true = true := by rw [hfa]; exact hzb
  have hmb' : st.mem.accessible m' 32 true = true := by rw [hfa]; exact hmb
  have hstk : st.mem.accessible (st.sp.toNat - 4096) 4296 true = true := by
    rw [hfa, hsp]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
  have hstkr : st.mem.accessible (st.sp.toNat - 4096) 4296 false = true := Janus.Arm64.Memory.accessible_read_of_write _ hstk
  have hacc8 : st.mem.accessible (st.sp.toNat - 8) 8 false = true := Janus.Arm64.Memory.accessible_mono _ hstkr (by omega) (by omega)
  have hacc0 : st.mem.accessible st.sp.toNat 8 false = true := Janus.Arm64.Memory.accessible_mono _ hstkr (by omega) (by omega)
  have hfo : ∀ a n, Outside a n (rt ++ [(s.sp.toNat - 4256, s.sp.toNat + 40)]) → st.mem.readLE a n = s.mem.readLE a n := fun a n h => hfr.readLE a n h
  have rdp : ∀ p k, Outside p 32 rt → Apart p 32 (s.sp.toNat - 4256) (4256 + 40) → k ≤ 24 →
      st.mem.readLE (p + k) 8 = s.mem.readLE (p + k) 8 := fun p k h1 h2 hk =>
    hfo _ _ (outside_stk (Outside.of_sub h1 (by omega) (by omega)) (by unfold Apart at h2; omega))
  have rx0 := rdp x.toNat 0 hxo hdx (by omega)
  have rx1 := rdp x.toNat 8 hxo hdx (by omega)
  have rx2 := rdp x.toNat 16 hxo hdx (by omega)
  have rx3 := rdp x.toNat 24 hxo hdx (by omega)
  have ry0 := rdp y.toNat 0 hyo hdy (by omega)
  have ry1 := rdp y.toNat 8 hyo hdy (by omega)
  have ry2 := rdp y.toNat 16 hyo hdy (by omega)
  have ry3 := rdp y.toNat 24 hyo hdy (by omega)
  simp only [Nat.add_zero] at rx0 ry0
  have hgv : st.mem.readLE ((st.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 := by
    rw [h28]; exact hfo _ _ (outside_stk hgo (by unfold Apart at hdg; omega))
  simp only [dm, reduceSegAddr, Nat.reduceAdd] at hpc
  have hret48 := hret.user
  have hspal : st.sp.toNat % 16 = 0 := by omega
  have hdz' : Apart z.toNat 32 (st.sp.toNat - 4096) 4296 := by unfold Apart at hdz ⊢; omega
  have hdx' : Apart x.toNat 32 (st.sp.toNat - 4096) 4296 := by unfold Apart at hdx ⊢; omega
  have hdy' : Apart y.toNat 32 (st.sp.toNat - 4096) 4296 := by unfold Apart at hdy ⊢; omega
  have hdm' : Apart m' 32 (st.sp.toNat - 4096) 4296 := by unfold Apart at hdm ⊢; omega
  have hspb : st.sp.toNat + 200 ≤ 2 ^ 48 := by omega
  have hsp344 : 344 ≤ st.sp.toNat := by omega
  have hdz0 := hdz
  have hdm0 := hdm
  have hzm0 := hzm
  have hxo0 := hxo
  have hyo0 := hyo
  have hdx0 := hdx
  have hdy0 := hdy
  clear hdz hdx hdy hdm hout hxo hyo hzo hfa rdp
  have hdg2 : (s.regs 28).toNat + 24 ≤ st.sp.toNat - 344 ∨ st.sp.toNat + 56 ≤ (s.regs 28).toNat := by
    unfold Apart at hdg; omega
  have hdg3 : (s.regs 28).toNat + 24 ≤ st.sp.toNat - 4096 ∨ st.sp.toNat + 200 ≤ (s.regs 28).toNat + 16 := by
    unfold Apart at hdg; omega
  have hnb := Fv256.Arm64.DivMLem.nb4 _ _ _ _ _ _ _ _ (by simpa using hx0) (by simpa using hx1) (by simpa using hx2) (by simpa using hx3) (by simpa using hy0) (by simpa using hy1) (by simpa using hy2) (by simpa using hy3)
  simp only [Nat.reducePow] at hnb
  janus_run [Util.readLE_32, hretslot, hbp, hz8, hacc8, hacc0, rx0, rx1, rx2, rx3, ry0, ry1, ry2, ry3, hgv,
    Janus.Tactic.sub_flags_c, BitVec.toNat_not, Util.readLE8_mod, Nat.reducePow, Nat.or_eq_zero_iff, Fv256.B.wv4_eq,
    Fv256.B.wv_writeLE_outside, Fv256.Arm64.DivLemmas.wv_zero4w, false_implies, BitVec.toNat_ofNat, Nat.zero_mod,
    Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff,
    Fv256.B.bv128_zero_toNat, Nat.zero_div, Fv256.B.ne_zero_of_limbs] until [dm + 0x130] calls [hU]
  all_goals (try simp only [Apart] at hzm0)
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *)
  all_goals (try simp only [hnb, Fv256.B.xor_eq_zero_nat] at *)
  case h =>
    rename_i a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte] at a0 a1 a2 a3 a4 a5 a6 a8 a9
    have hsp0 : st.sp.toNat = s.sp.toNat - 160 := hsp
    obtain ⟨MM, hMM⟩ : ∃ MM, MM = ((((((((st.mem.writeLE (st.sp.toNat + 144) 8 m').writeLE (st.sp.toNat + 112) 8 0).writeLE
        (st.sp.toNat + 120) 8 0).writeLE (st.sp.toNat + 128) 8 0).writeLE (st.sp.toNat + 136) 8 0).writeLE
        (st.sp.toNat + 80) 8 0).writeLE (st.sp.toNat + 88) 8 0).writeLE (st.sp.toNat + 96) 8 0).writeLE (st.sp.toNat + 104) 8 0 := ⟨_, rfl⟩
    have hMMf : MemFrame st.mem MM [(st.sp.toNat + 80, st.sp.toNat + 152)] := by
      rw [hMM]; janus_frame
    have hpcS : s'.pc = BitVec.ofNat 64 (dm + 0x130) := by
      simp only [dm, reduceSegAddr, Nat.reduceAdd]; exact a0
    have hsp2 : s'.sp = st.sp := a2
    have hspb' : st.sp.toNat + 200 ≤ 2 ^ 48 := hspb
    have e112 : (st.sp + 112#64).toNat = st.sp.toNat + 112 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have e80 : (st.sp + 80#64).toNat = st.sp.toNat + 80 := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [e112] at a8
    rw [e80] at a9
    simp (config := { decide := true }) only [setReg_apply, ↓reduceIte, e112, e80] at a10
    rw [← hMM] at a10 a8 a9
    have hMM144 : MM.readLE (st.sp.toNat + 144) 8 = m' := by
      rw [hMM]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨gf0, gf, g0, g1, g2, g3, g4, g5⟩ := Fv256.Arm64.DivMGlue.glue rt s.sp.toNat z.toNat x.toNat y.toNat m' ret (s.regs 29).toNat
      s.mem st.mem MM s'.mem hb hxo0 hyo0 (by unfold Apart at hdx0; omega) (by unfold Apart at hdy0; omega) hfr (by rw [hsp0] at hMMf; exact hMMf) (by rw [hsp0] at hMM144; exact hMM144)
      (by rw [hsp0] at a10; exact a10) (by rw [hsp0] at hretslot; exact hretslot) (by rw [hsp0] at hbp; exact hbp) (by rw [hsp0] at hz8; exact hz8)
    have hyne : s.mem.readLE y.toNat 32 ≠ 0 := by rw [Util.readLE_32]; omega
    have hS : s'.sp.toNat = s.sp.toNat - 160 := by rw [hsp2]; exact hsp0
    rw [g4, g5] at a8
    rw [g4, g5] at a9
    have hq : Fv256.B.wv s'.mem (s'.sp.toNat + 112) 4 = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) := by
      rw [hS, show s.sp.toNat - 160 = st.sp.toNat by omega, a8, Fv256.B.wv4_eq, Fv256.B.wv4_eq]
      show _ = Fv256.B.divSpec (s.mem.readLE x.toNat 32) (s.mem.readLE y.toNat 32)
      rw [Fv256.B.divSpec_of_ne _ _ hyne]
    have hr : Fv256.B.wv s'.mem (s'.sp.toNat + 80) 4 = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) := by
      rw [hS, show s.sp.toNat - 160 = st.sp.toNat by omega, a9, Fv256.B.wv4_eq, Fv256.B.wv4_eq]
      show _ = Fv256.B.modSpec (s.mem.readLE x.toNat 32) (s.mem.readLE y.toNat 32)
      rw [Fv256.B.modSpec_of_ne _ _ hyne]
    have hC := partC rt z.toNat m' ret _ _ hret s s' hal hb ha (by unfold Apart at hdz0; omega) (by unfold Apart at hdm0; omega) hzm0 hza hma hpcS hS (by rw [a3]; exact h18) (by rw [a4]; exact h28)
      gf0 hw hzb hmb (by rw [hS]; exact g0) (by rw [hS]; exact g1) (by rw [hS]; exact g2) (by rw [hS]; exact g3) hq hr
    refine Fv256.H.reaches_mono hC ?_
    intro o ho
    cases o with
    | returned S => 
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := ho
      exact ⟨c1, by rw [c2]; simp, _, c3, rfl, c4, c5, c6⟩
    | stub _ _ _ => exact ho.elim
  all_goals (first
    | (refine ⟨?spgoal, m', rfl, rfl, ?_, ?_, ?_⟩
       case spgoal => (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := s.sp.isLt; omega))
    | skip)
  all_goals (first | janus_frame | skip)
  all_goals (
    try set_option maxHeartbeats 300000 in simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside,
      Janus.Arm64.Memory.readLE_writeLE_self, Nat.zero_div, Nat.zero_mod, Nat.reducePow, Nat.sub_self, Nat.pow_zero, Nat.div_one,
      Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right, Fv256.B.modSpec_zero_left, Fv256.B.modSpec_zero_right, Util.readLE8_mod])
  all_goals (
    first
    | with_reducible assumption
    | (rw [Fv256.B.divSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | with_reducible exact Fv256.B.one_eq_div _ _ (by omega) (by omega)
           | with_reducible exact (Nat.div_eq_of_lt (by omega)).symm
           | with_reducible exact Fv256.B.div_congr _ _ _ (by omega)))
    | (rw [Fv256.B.modSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | with_reducible exact Fv256.B.zero_eq_mod_self _ _ (by omega)
           | with_reducible exact (Nat.mod_eq_of_lt (by omega)).symm
           | with_reducible exact Fv256.B.mod_congr _ _ _ (by omega)))
    | (exfalso; omega)
    | (have e1 : s.mem.readLE (y.toNat + 8) 8 = 0 := by omega
       have e2 : s.mem.readLE (y.toNat + 16) 8 = 0 := by omega
       have e3 : s.mem.readLE (y.toNat + 24) 8 = 0 := by omega
       rw [e1, e2, e3]
       simp only [Nat.mul_zero, Nat.add_zero]
       first
         | with_reducible exact div64_goal _ _ hx0 (by omega)
         | with_reducible exact mod64_goal _ _ hx0 (by omega))
    | skip)

end Fv256.Arm64.DivModLib
