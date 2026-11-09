import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.UdivMathB
import Fv256.Proofs.Common.UdivremMath
import Fv256.Proofs.Common.KnuthMathB
import Fv256.Proofs.Arm64.UdivremFront
import Fv256.Proofs.Arm64.By1
import Fv256.Proofs.Arm64.UdivremA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremFront

namespace Fv256.Arm64.UdivremB

theorem ofNat_toNat' (x : W64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem caseOne (T : State) (ret : W64) (Q : State → Prop) (M0 M5 : Memory) (R : Nat → W64) (fl : Flags)
    (qp up dp remp L ulen s x29 x30 : Nat)
    (F : Front T.sp.toNat M0 M5 qp up dp remp L 1 ulen s x29 x30)
    (hx30a : x30 % 4 = 0) (hx30b : x30 < 2 ^ 56)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hW : M0.accessible (T.sp.toNat - 120) 416 true = true)
    (hL : L ≤ 8) (hqb : qp + 8 * L ≤ 2 ^ 48) (hqa : M0.accessible qp (8 * L) true = true)
    (hqs : qp + 8 * L ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ qp)
    (hq0 : Fv256.B.wv M0 qp L = 0)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ (remp + 32 ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ remp) ∧
      (qp + 8 * L ≤ remp ∨ remp + 32 ≤ qp))
    (hremp : remp < 2 ^ 64)
    (hg1 : (R 28).toNat + 24 ≤ 2 ^ 48) (hg2 : M0.accessible ((R 28).toNat + 16) 8 false = true)
    (hg3 : M0.readLE ((R 28).toNat + 16) 8 + 48 < T.sp.toNat)
    (hgd : (R 28).toNat + 24 ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ (R 28).toNat + 16)
    (r0 : R 0 = BitVec.ofNat 64 qp) (r1 : R 1 = BitVec.ofNat 64 L) (r14 : R 14 = BitVec.ofNat 64 (T.sp.toNat + 80))
    (r15 : R 15 = BitVec.ofNat 64 (ulen + 1)) 
    (hQ : ∀ (U : State) (R' : Nat → W64) (fl' : Flags) (Mf : Memory), U.sp = T.sp → FinOK L M0 Mf qp up dp remp (T.sp.toNat + 224) →
      R' 29 = BitVec.ofNat 64 x29 → R' 30 = BitVec.ofNat 64 x30 → (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R' i = R i) →
      Q { U with regs := R', sp := U.sp + 224#64, pc := BitVec.ofNat 64 x30, flags := fl', mem := Mf }) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 x30) { T with regs := R, pc := BitVec.ofNat 64 by1pc, flags := fl, mem := M5 } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : by1pc
  simp only [hh1]
  have hM5a : M5.accessible (T.sp.toNat - 120) 416 true = true := by rw [F.frame.accessible]; exact hW
  have hm : (ulen + 1) % 18446744073709551616 = ulen + 1 := Nat.mod_eq_of_lt (by have := F.hulen; omega)
  have hu1 : 1 ≤ ulen := by have := F.hnu; omega
  have hul := F.hulen
  have hgg2 : M5.accessible ((R 28).toNat + 16) 8 false = true := by rw [F.frame.accessible]; exact hg2
  have hgg3 : M5.readLE ((R 28).toNat + 16) 8 + 48 < T.sp.toNat := by
    rw [F.frame.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hg3
  have hdn0 : 2 ^ 63 ≤ M5.readLE (T.sp.toNat + 160) 8 := by simpa using F.dntop
  have hqa5 : M5.accessible qp (8 * ulen) true = true := by
    rw [F.frame.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hqa (by omega) (by have := F.hulen; omega)
  have hua5 : M5.accessible (T.sp.toNat + 80) (8 * (ulen + 1)) false = true := by
    apply Janus.Arm64.Memory.accessible_read_of_write
    exact Janus.Arm64.Memory.accessible_mono _ hM5a (by omega) (by have := F.hulen; omega)
  have htop : M5.readLE (T.sp.toNat + 80 + 8 * ulen) 8 < M5.readLE (T.sp.toNat + 160) 8 := by
    have h1 := Fv256.B.wv_ge_top M5 (T.sp.toNat + 80) (ulen + 1) (by omega)
    rw [show ulen + 1 - 1 = ulen by omega, F.un] at h1
    have h2 := Fv256.B.wv_lt M0 up ulen
    have h3 : Fv256.B.wv M0 up ulen * 2 ^ s < 2 ^ (64 * ulen) * 2 ^ s := Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos s)
    have h4 : M5.readLE (T.sp.toNat + 80 + 8 * ulen) 8 < 2 ^ s := by
      rcases Nat.lt_or_ge (M5.readLE (T.sp.toNat + 80 + 8 * ulen) 8) (2 ^ s) with hc | hc
      · exact hc
      · exfalso
        have : 2 ^ s * 2 ^ (64 * ulen) ≤ M5.readLE (T.sp.toNat + 80 + 8 * ulen) 8 * 2 ^ (64 * ulen) :=
          Nat.mul_le_mul_right _ hc
        rw [Nat.mul_comm (2 ^ s)] at this
        omega
    have h5 : 2 ^ s ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by have := F.hs; omega)
    have h6 := F.dntop
    simp at h6 ⊢
    omega
  have hs30 := F.s_x30
  have hs29 := F.s_x29
  janus_run [r0, r1, r14, r15, hm, hs30, hs29] until [ku + 0x244] calls [hc := Fv256.Arm64.By1.by1_summary]
  have cpc : s'.pc = BitVec.ofNat 64 by1ret := by
    have := ‹s'.pc = _›
    janus_eval_nat hbr : by1ret
    simpa [setReg, hbr] using this
  have cf := ‹MemFrame _ s'.mem _›
  have csp : s'.sp = T.sp := ‹s'.sp = _›
  have cr0 : BitVec.toNat (s'.regs 0) < M5.readLE (BitVec.toNat T.sp + 160) 8 := ‹_›
  have cwv : Fv256.B.wv M5 (T.sp.toNat + 80) (ulen + 1) = M5.readLE (T.sp.toNat + 160) 8 * Fv256.B.wv s'.mem qp ulen + (s'.regs 0).toNat := ‹_›
  have cu := ‹∀ i : Nat, ¬ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → s'.regs i = _›
  have e : ({ s' with regs := s'.regs, pc := BitVec.ofNat 64 by1ret, flags := s'.flags, mem := s'.mem } : State) = s' := by
    cases s'; simp only at cpc; subst cpc; rfl
  have key := Fv256.Arm64.UdivremA.by1tail s' (BitVec.ofNat 64 x30) Q s'.mem s'.regs s'.flags remp s (s'.regs 0).toNat x29 x30 F.hs (s'.regs 0).isLt hx30a hx30b
    (by rw [csp]; exact hal) (by rw [csp]; omega) (by rw [csp]; omega) ?hMc ?hremb hremp (ofNat_toNat' _).symm ?hsrem ?hss ?h29 ?h30 ?hQ'
  rw [e] at key
  exact key
  case hMc =>
    rw [csp, cf.accessible, F.frame.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hW (by omega) (by omega)
  case hremb =>
    intro hr
    obtain ⟨h1, h2, h3, h4⟩ := hrem hr
    refine ⟨h1, ?_, ?_⟩
    · rw [cf.accessible, F.frame.accessible]; exact h2
    · rw [csp]; omega
  case hsrem =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := F.hulen; omega)]
    exact F.s_rem
  case hss =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := F.hulen; omega)]
    exact F.s_s
  case h29 =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := F.hulen; omega)]
    exact F.s_x29
  case h30 =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := F.hulen; omega)]
    exact F.s_x30
  case hQ' =>
    intro R' fl' Mf h29' h30' hRu' hMf hMf0
    -- the arithmetic
    have hd0 : M0.readLE dp 8 ≠ 0 := by simpa using F.dtop
    have hdwv : Fv256.B.wv M0 dp 4 = M0.readLE dp 8 := by rw [F.dwv]; simp [Fv256.B.wv]
    have hdn0 : M5.readLE (T.sp.toNat + 160) 8 = M0.readLE dp 8 * 2 ^ s := by
      have := F.dn; simpa [Fv256.B.wv] using this
    have hU : Fv256.B.wv M0 up L = Fv256.B.wv M0 up ulen := F.uwv
    have hun := F.un
    rw [cwv] at hun
    rw [hdn0] at hun cr0
    have hnd := Fv256.B.norm_div_eq (Fv256.B.wv M0 up ulen) (M0.readLE dp 8) (2 ^ s) (Fv256.B.wv s'.mem qp ulen) (s'.regs 0).toNat
      (Nat.two_pow_pos s) (Nat.pos_of_ne_zero hd0) hun.symm cr0
    obtain ⟨hQe, hRe⟩ := hnd
    have hr1s : (s'.regs 0).toNat / 2 ^ s = Fv256.B.wv M0 up ulen % M0.readLE dp 8 := by
      rw [hRe]; exact Nat.mul_div_cancel _ (Nat.two_pow_pos s)
    have hul := F.hulen
    have hqz : ∀ j, ulen ≤ j → j < L → s'.mem.readLE (qp + 8 * j) 8 = 0 := by
      intro j h1 h2
      rw [cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), F.frame.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact Fv256.B.wv_zero_word M0 qp L hq0 j h2
    have hwq : Fv256.B.wv s'.mem qp L = Fv256.B.wv s'.mem qp ulen := Fv256.B.wv_ext s'.mem qp ulen L hul hqz
    have hQL : Fv256.B.wv s'.mem qp L = Fv256.B.wv M0 up L / Fv256.B.wv M0 dp 4 := by
      rw [hwq, hQe, hU, hdwv]
    have hF1 : MemFrame M0 s'.mem [(qp, qp + 8 * L), (T.sp.toNat - 120, T.sp.toNat + 216), (T.sp.toNat + 232, T.sp.toNat + 296)] := by
      refine (F.frame.trans cf ?_)
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega
    have hQ := hQ s' R' fl' Mf csp
    refine hQ ⟨?_, ?_, ?_, ?_⟩ h29' h30' ?_
    · by_cases hr0 : remp = 0
      · rw [hMf0 hr0, hQL]
      · obtain ⟨_, _, _, h4⟩ := hrem hr0
        obtain ⟨_, _, _, _, hfm⟩ := hMf hr0
        rw [Fv256.B.wv_of_frame s'.mem Mf [(remp, remp + 32)] hfm qp L (by simp only [outside_cons, outside_nil, and_true]; omega), hQL]
    · intro hr0
      obtain ⟨h1, h2, h3, h4, hfm⟩ := hMf hr0
      have e : Fv256.B.wv Mf remp 4 = Mf.readLE remp 8 + 2 ^ 64 * (Mf.readLE (remp + 8) 8 + 2 ^ 64 * (Mf.readLE (remp + 16) 8 + 2 ^ 64 * (Mf.readLE (remp + 24) 8 + 2 ^ 64 * 0))) := by
        simp only [Fv256.B.wv]
      rw [e, h1, h2, h3, h4, hr1s, hU, hdwv]
      simp
    · intro hr0
      rw [hMf0 hr0]
      exact hF1.mono (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    · intro hr0
      obtain ⟨_, _, _, _, hfm⟩ := hMf hr0
      exact hF1.trans hfm (by intro a n h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hRu' i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega), cu i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
      repeat' rw [if_neg (by omega)]

end Fv256.Arm64.UdivremB
