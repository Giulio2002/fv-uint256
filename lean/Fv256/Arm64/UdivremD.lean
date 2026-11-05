import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.KnuthMathB
import Fv256.Arm64.UdivremFront
import Fv256.Arm64.UdivremA

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremFront

namespace Fv256.Arm64.UdivremD

/-- The statement of `Fv256.Arm64.KnuthSummary.knuth_summary` (FV-H), as a proposition. -/
def KnuthStmt : Prop :=

    Summary Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth")
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 80 ∧ StackOK s 120 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        2 ≤ (s.regs 7).toNat ∧ (s.regs 7).toNat ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat < 2 ^ 20 ∧
        (s.regs 4).toNat ≤ (s.regs 5).toNat ∧ (s.regs 5).toNat < 2 ^ 55 ∧
        (s.regs 4).toNat - (s.regs 7).toNat ≤ (s.regs 1).toNat ∧ (s.regs 1).toNat < 2 ^ 20 ∧
        (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * (s.regs 4).toNat) true = true ∧
        (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat (8 * (s.regs 7).toNat) false = true ∧
        (s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * (s.regs 1).toNat) true = true ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ (s.regs 6).toNat ∨ (s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 8 * (s.regs 7).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        ((s.regs 0).toNat + 8 * (s.regs 1).toNat ≤ s.sp.toNat - 120 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        2 ^ 63 ≤ s.mem.readLE ((s.regs 6).toNat + 8 * ((s.regs 7).toNat - 1)) 8 ∧
        Fv256.B.wv s.mem ((s.regs 3).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)) (s.regs 7).toNat <
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧ (∀ i, 22 ≤ i → s'.regs i = s.regs i) ∧
        Fv256.B.wv s.mem (s.regs 3).toNat (s.regs 4).toNat =
          Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat * Fv256.B.wv s'.mem (s.regs 0).toNat ((s.regs 4).toNat - (s.regs 7).toNat) +
            Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat ∧
        Fv256.B.wv s'.mem (s.regs 3).toNat (s.regs 7).toNat < Fv256.B.wv s.mem (s.regs 6).toNat (s.regs 7).toNat ∧
        MemFrame s.mem s'.mem [((s.regs 3).toNat, (s.regs 3).toNat + 8 * (s.regs 4).toNat),
          ((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - (s.regs 7).toNat)),
          (s.sp.toNat - 120, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)])

abbrev knuth : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivremKnuth"

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem caseK (hKn : KnuthStmt) (T : State) (ret : W64) (Q : State → Prop) (M0 M5 : Memory) (R : Nat → W64) (fl : Flags)
    (qp up dp remp L n ulen s x29 x30 : Nat)
    (F : Front T.sp.toNat M0 M5 qp up dp remp L n ulen s x29 x30) (hn2 : 2 ≤ n)
    (hx30a : x30 % 4 = 0) (hx30b : x30 < 2 ^ 56)
    (hal : T.sp.toNat % 16 = 0) (hsp : 0x138 ≤ T.sp.toNat) (hspb : T.sp.toNat + 0x138 ≤ 2 ^ 48)
    (hW : M0.accessible (T.sp.toNat - 120) 416 true = true)
    (hL : L ≤ 8) (hqb : qp + 8 * L ≤ 2 ^ 48) (hqa : M0.accessible qp (8 * L) true = true)
    (hqs : qp + 8 * L ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ qp)
    (hq0 : Fv256.B.wv M0 qp L = 0)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ (remp + 32 ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ remp) ∧
      (qp + 8 * L ≤ remp ∨ remp + 32 ≤ qp) ∧ Fv256.B.wv M0 remp 4 = 0)
    (hremp : remp < 2 ^ 64)
    (hg1 : (R 28).toNat + 24 ≤ 2 ^ 48) (hg2 : M0.accessible ((R 28).toNat + 16) 8 false = true)
    (hg3 : M0.readLE ((R 28).toNat + 16) 8 + 80 < T.sp.toNat)
    (hgd : (R 28).toNat + 24 ≤ T.sp.toNat - 120 ∨ T.sp.toNat + 296 ≤ (R 28).toNat + 16)
    (r0 : R 0 = BitVec.ofNat 64 qp) (r1 : R 1 = BitVec.ofNat 64 L)
    (r3 : R 3 = BitVec.ofNat 64 (T.sp.toNat + 80)) (r4 : R 4 = BitVec.ofNat 64 (ulen + 1)) (r5 : R 5 = 9#64)
    (r6 : R 6 = BitVec.ofNat 64 (T.sp.toNat + 160)) (r7 : R 7 = BitVec.ofNat 64 n) (r8 : R 8 = 4#64)
    (hs30 : M5.readLE T.sp.toNat 8 = x30)
    (hsn : M5.readLE (T.sp.toNat + 200) 8 = n - 1) (hsu5 : M5.readLE (T.sp.toNat + 152) 8 = ulen + 1) (hsc5 : M5.readLE (T.sp.toNat + 192) 8 = 64 - s)
    (hQ : ∀ (U : State) (R' : Nat → W64) (fl' : Flags) (Mf : Memory), U.sp = T.sp → FinOK L M0 Mf qp up dp remp (T.sp.toNat + 224) →
      R' 29 = BitVec.ofNat 64 x29 → R' 30 = BitVec.ofNat 64 x30 → (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 29, 30] → R' i = R i) →
      Q { U with regs := R', sp := U.sp + 224#64, pc := BitVec.ofNat 64 x30, flags := fl', mem := Mf }) :
    ReachesRet Extracted.program (BitVec.ofNat 64 x30) { T with regs := R, pc := BitVec.ofNat 64 knpc, flags := fl, mem := M5 } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : knpc
  simp only [hh1]
  have hul := F.hulen
  have hnu := F.hnu
  have hs := F.hs
  have hm : (ulen + 1) % 18446744073709551616 = ulen + 1 := Nat.mod_eq_of_lt (by omega)
  have hM5W : M5.accessible (T.sp.toNat - 120) 416 true = true := by rw [F.frame.accessible]; exact hW
  have hgg2 : M5.accessible ((R 28).toNat + 16) 8 false = true := by rw [F.frame.accessible]; exact hg2
  have hgg3 : M5.readLE ((R 28).toNat + 16) 8 + 80 < T.sp.toNat := by
    rw [F.frame.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hg3
  have hqa5 : M5.accessible qp (8 * L) true = true := by rw [F.frame.accessible]; exact hqa
  have hun5 : M5.accessible (T.sp.toNat + 80) (8 * (ulen + 1)) true = true :=
    Janus.Arm64.Memory.accessible_mono _ hM5W (by omega) (by omega)
  have hdn5 : M5.accessible (T.sp.toNat + 160) (8 * n) false = true :=
    Janus.Arm64.Memory.accessible_read_of_write _ (Janus.Arm64.Memory.accessible_mono _ hM5W (by omega) (by have := F.hn4; omega))
  have hlt : Fv256.B.wv M5 (T.sp.toNat + 80 + 8 * (ulen + 1 - n)) n < Fv256.B.wv M5 (T.sp.toNat + 160) n := by
    have h1 := Fv256.B.knuth_pre_lt M5 (T.sp.toNat + 80) ulen n s (Fv256.B.wv M0 up ulen) (Fv256.B.wv M5 (T.sp.toNat + 160) n) (by omega) hnu hs
      (Fv256.B.wv_lt M0 up ulen) F.un
      (by
        have h2 := Fv256.B.wv_ge_top M5 (T.sp.toNat + 160) n (by omega)
        have h3 := F.dntop
        have h4 : 2 ^ 63 * 2 ^ (64 * (n - 1)) ≤ M5.readLE (T.sp.toNat + 160 + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) :=
          Nat.mul_le_mul_right _ h3
        omega)
    exact h1
  have htopn : 2 ^ 63 ≤ M5.readLE (T.sp.toNat + 160 + 8 * (n - 1)) 8 := F.dntop
  janus_run [r0, r1, r3, r4, r5, r6, r7, r8, hm] until [ku + 0x210] calls [hc := hKn]
  have cpc : s'.pc = BitVec.ofNat 64 knret := by
    have := ‹s'.pc = _›
    janus_eval_nat hbr : knret
    simpa [setReg, hbr] using this
  have cf := ‹MemFrame M5 s'.mem _›
  have csp : s'.sp = T.sp := ‹s'.sp = _›
  have cwv := ‹Fv256.B.wv M5 (T.sp.toNat + 80) (ulen + 1) = _›
  have clt := ‹Fv256.B.wv s'.mem (T.sp.toNat + 80) n < _›
  have cu := ‹∀ i : Nat, 22 ≤ i → s'.regs i = _›
  have e : ({ s' with regs := s'.regs, pc := BitVec.ofNat 64 knret, flags := s'.flags, mem := s'.mem } : State) = s' := by
    cases s'; simp only at cpc; subst cpc; rfl
  have hkr : knret = 767136 := by
    janus_eval_nat hh : knret
    exact hh
  have hdn0 : 0 < Fv256.B.wv M0 dp n := by
    have h := Fv256.B.wv_ge_top M0 dp n (by omega)
    have : 0 < M0.readLE (dp + 8 * (n - 1)) 8 * 2 ^ (64 - 64 + 64 * (n - 1)) := Nat.mul_pos (Nat.pos_of_ne_zero F.dtop) (Nat.two_pow_pos _)
    simp only [Nat.sub_self, Nat.zero_add] at this
    omega
  have key := Fv256.Arm64.UdivremA.kntail s' (BitVec.ofNat 64 x30) Q s'.mem s'.regs s'.flags remp n ulen s x29 x30 hn2 F.hn4 hnu (by omega) hs hx30a hx30b
    (by rw [csp]; exact hal) (by rw [csp]; exact hsp) (by rw [csp]; exact hspb)
    ?hMc ?hremb hremp ?hsrem ?hss ?hsn' ?hsu' ?hsc' ?h29 ?h30 ?hQ'
  rw [e] at key
  exact key
  case hMc =>
    rw [csp, cf.accessible, F.frame.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hW (by omega) (by omega)
  case hremb =>
    intro hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrem hr
    refine ⟨h1, ?_, by rw [csp]; omega⟩
    rw [cf.accessible, F.frame.accessible]; exact h2
  case hsrem =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact F.s_rem
  case hss =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact F.s_s
  case hsn' =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hsn
  case hsu' =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hsu5
  case hsc' =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hsc5
  case h29 =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact F.s_x29
  case h30 =>
    rw [csp, cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hs30
  case hQ' =>
    intro R' fl' Mf h29' h30' hRu' hMf hMf0
    simp only [csp] at hMf
    have hD0 : 0 < Fv256.B.wv M0 dp n := hdn0
    have hun := F.un
    rw [cwv, F.dn] at hun
    have hnd := Fv256.B.norm_div_eq (Fv256.B.wv M0 up ulen) (Fv256.B.wv M0 dp n) (2 ^ s) (Fv256.B.wv s'.mem qp (ulen + 1 - n)) (Fv256.B.wv s'.mem (T.sp.toNat + 80) n)
      (Nat.two_pow_pos s) hD0 hun.symm (by rw [F.dn] at clt; exact clt)
    obtain ⟨hQe, hRe⟩ := hnd
    have hr1s : Fv256.B.wv s'.mem (T.sp.toNat + 80) n / 2 ^ s = Fv256.B.wv M0 up ulen % Fv256.B.wv M0 dp n := by
      rw [hRe]; exact Nat.mul_div_cancel _ (Nat.two_pow_pos s)
    have hqz : ∀ j, ulen + 1 - n ≤ j → j < L → s'.mem.readLE (qp + 8 * j) 8 = 0 := by
      intro j h1 h2
      rw [cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega), F.frame.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact Fv256.B.wv_zero_word M0 qp L hq0 j h2
    have hwq : Fv256.B.wv s'.mem qp L = Fv256.B.wv s'.mem qp (ulen + 1 - n) := Fv256.B.wv_ext s'.mem qp (ulen + 1 - n) L (by omega) hqz
    have hQL : Fv256.B.wv s'.mem qp L = Fv256.B.wv M0 up L / Fv256.B.wv M0 dp 4 := by
      rw [hwq, hQe, F.uwv, F.dwv]
    have hF1 : MemFrame M0 s'.mem [(qp, qp + 8 * L), (T.sp.toNat - 120, T.sp.toNat + 216), (T.sp.toNat + 232, T.sp.toNat + 296)] := by
      refine (F.frame.trans cf ?_)
      intro a n' h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega
    refine hQ s' R' fl' Mf csp ⟨?_, ?_, ?_, ?_⟩ h29' h30' ?_
    · by_cases hr0 : remp = 0
      · rw [hMf0 hr0, hQL]
      · obtain ⟨_, _, _, h4, _⟩ := hrem hr0
        obtain ⟨_, _, hfm⟩ := hMf hr0
        rw [Fv256.B.wv_of_frame s'.mem Mf [(remp, remp + 8 * n)] hfm qp L (by simp only [outside_cons, outside_nil, and_true]; have := F.hn4; omega), hQL]
    · intro hr0
      obtain ⟨hlow, hlast, hfm⟩ := hMf hr0
      obtain ⟨_, _, _, h4, h5⟩ := hrem hr0
      have hz : ∀ j, n ≤ j → j < 4 → Mf.readLE (remp + 8 * j) 8 = 0 := by
        intro j h1 h2
        rw [hfm.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          F.frame.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
        exact Fv256.B.wv_zero_word M0 remp 4 h5 j h2
      have hw4 : Fv256.B.wv Mf remp 4 = Fv256.B.wv Mf remp n := Fv256.B.wv_ext Mf remp n 4 F.hn4 hz
      have hsr := Fv256.B.shr_vec s'.mem Mf s (by omega) n (T.sp.toNat + 80) remp (by
        intro i hi
        by_cases hin : i + 1 < n
        · rw [if_pos hin]; exact hlow i (by omega)
        · rw [if_neg hin]
          have : i = n - 1 := by omega
          subst this
          rw [hlast]; omega)
      rw [hw4, hsr, hr1s, F.uwv, F.dwv]
    · intro hr0
      rw [hMf0 hr0]
      exact hF1.mono (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
    · intro hr0
      obtain ⟨_, _, hfm⟩ := hMf hr0
      have := hF1.trans hfm (rs'' := [(qp, qp + 8 * L), (remp, remp + 32), (T.sp.toNat + 224 - 344, T.sp.toNat + 224 - 8), (T.sp.toNat + 224 + 8, T.sp.toNat + 224 + 72)])
        (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; have := F.hn4; omega)
      exact this
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hRu' i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega), cu i (by omega)]
      rw [if_neg (by omega)]

end Fv256.Arm64.UdivremD
