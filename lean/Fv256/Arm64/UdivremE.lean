import Fv256.Arm64.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.KnuthMathB
import Fv256.Arm64.UdivremFront
import Fv256.Arm64.UdivremA
import Fv256.Arm64.UdivremB
import Fv256.Arm64.UdivremC
import Fv256.Arm64.UdivremD

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremFront Fv256.Arm64.UdivremD

namespace Fv256.Arm64.UdivremE

theorem bv_toNat_ofNat_lt' (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem ofNat_toNat' (x : W64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

/-- The postcondition of the arm64 `udivrem` summary (`sp0 = s.sp`, the entry stack pointer). -/
def UPost (L : Nat) (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
    s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
    (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
    FinOK L s.mem s'.mem (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat (s.regs 7).toNat s.sp.toNat

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
theorem udivrem_summary_L {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) (hKn : KnuthStmt) :
    Summary Fv256.Arm64.ChainProg.program ku
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 304 ∧ StackOK s 344 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 1).toNat = L ∧ (s.regs 4).toNat = L ∧
        (s.regs 0).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * L) true = true ∧
        (s.regs 3).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * L) false = true ∧
        (s.regs 6).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat 32 false = true ∧
        ((s.regs 0).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        Fv256.B.wv s.mem (s.regs 6).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧
        ((s.regs 7).toNat ≠ 0 → (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 7).toNat 32 true = true ∧
          Fv256.B.wv s.mem (s.regs 7).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 3).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 3).toNat) ∧
          ((s.regs 7).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 7).toNat)))
      (UPost L) := by
  intro s hpc ⟨h30a, h30b, hgd, hst, hgw, hq1, hu4, hqb, hqa, hub, hua, hdb, hda, hqs, hus, hds, hD0, hq0, hrem⟩
  have e0 := (ofNat_toNat' (s.regs 0)).symm
  have e1 := (ofNat_toNat' (s.regs 1)).symm
  have e3 := (ofNat_toNat' (s.regs 3)).symm
  have e4 := (ofNat_toNat' (s.regs 4)).symm
  have e6 := (ofNat_toNat' (s.regs 6)).symm
  have e7 := (ofNat_toNat' (s.regs 7)).symm
  have e28 := (ofNat_toNat' (s.regs 28)).symm
  have e30 := (ofNat_toNat' (s.regs 30)).symm
  have e29 := (ofNat_toNat' (s.regs 29)).symm
  have hq64 := (s.regs 0).isLt
  have hu64 := (s.regs 3).isLt
  have hd64 := (s.regs 6).isLt
  have hr64 := (s.regs 7).isLt
  have hx30 : (s.regs 30).toNat < 2 ^ 64 := (s.regs 30).isLt
  show ReachesRet Fv256.Arm64.ChainProg.program (s.regs 30) s _
  obtain ⟨hg1, hg2, hg3⟩ := hgd
  obtain ⟨hsal, hsb, hsc, hsw⟩ := hst
  rw [e30]
  refine pro1 s (BitVec.ofNat 64 (s.regs 30).toNat) _ hpc ⟨hg1, hg2, by omega⟩ ⟨hsal, by omega, hsc, Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)⟩ ?k1
  intro R1 fl1 M1 r5 r29 hRu1 hfr1 hx30m hx29m hq0m hu0m
  -- the frame after the prologue
  let T : State := { s with sp := s.sp - 224#64 }
  have hTsp : T.sp.toNat = s.sp.toNat - 224 := by
    show (s.sp - 224#64).toNat = _
    rw [BitVec.toNat_sub, bv_toNat_ofNat_lt' 224 (by omega)]; omega
  have hR1_6 : R1 6 = BitVec.ofNat 64 (s.regs 6).toNat := (hRu1 6 (by simp)).trans e6.symm.symm
  have hda1 : M1.accessible (s.regs 6).toNat 32 false = true := by rw [hfr1.accessible]; exact hda
  have hw1 : Fv256.B.wv M1 (s.regs 6).toNat 4 = Fv256.B.wv s.mem (s.regs 6).toNat 4 :=
    Fv256.B.wv_of_frame s.mem M1 _ hfr1 _ 4 (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine dlen_loop T (BitVec.ofNat 64 (s.regs 30).toNat) _ (s.regs 6).toNat M1 R1 hdb hda1 ?kd 4 R1 fl1 (Nat.le_refl _) hR1_6
    (by rw [r5]; decide) (fun k hk => rfl) (fun j h1 h2 => absurd h2 (by omega))
  intro R2 fl2 n r9 hn4 hz hnz hRu2
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; apply hD0
      rw [← hw1, Fv256.B.wv_ext M1 (s.regs 6).toNat n 4 (by omega) (fun j hj1 hj2 => hz j hj1 hj2)]
      subst h; rfl
    · exact h
  have hnz1 := hnz hn1
  have hs4 : s.regs 4 = BitVec.ofNat 64 L := by rw [← hu4]; exact e4
  have hs1 : s.regs 1 = BitVec.ofNat 64 L := by rw [← hq1]; exact e1
  have hal : T.sp.toNat % 16 = 0 := by rw [hTsp]; omega
  have hMs1 : M1.accessible T.sp.toNat 296 true = true := by
    rw [hfr1.accessible, hTsp]; exact Janus.Arm64.Memory.accessible_mono _ hsw (by omega) (by omega)
  have hMa0 : M1.accessible (T.sp.toNat + 160) 32 true = true := Janus.Arm64.Memory.accessible_mono _ hMs1 (by omega) (by omega)
  have hdisjd : (s.regs 6).toNat + 32 ≤ T.sp.toNat + 160 ∨ T.sp.toNat + 192 ≤ (s.regs 6).toNat := by rw [hTsp]; omega
  have hR2_6 : R2 6 = BitVec.ofNat 64 (s.regs 6).toNat := (hRu2 6 (by simp)).trans hR1_6
  have hR1_4 : R1 4 = BitVec.ofNat 64 L := (hRu1 4 (by simp)).trans hs4
  have hR2_4 : R2 4 = BitVec.ofNat 64 L := (hRu2 4 (by simp)).trans hR1_4
  refine pro2 T _ _ (s.regs 6).toNat n M1 R2 fl2 hn1 hn4 r9 hR2_6 hdb hda1 hnz1 (by rw [hTsp]; omega) (by rw [hTsp]; omega) hal hMs1 ?kp2
  intro R3 fl3 M3 sh hsh63 hshc r10 r5' r9' r11 r12 r13 hRu3 hfr3 hz3
  have hR3_6 : R3 6 = BitVec.ofNat 64 (s.regs 6).toNat := (hRu3 6 (by simp)).trans hR2_6
  have hR3_4 : R3 4 = BitVec.ofNat 64 L := (hRu3 4 (by simp)).trans hR2_4
  refine dn_loop T _ _ (s.regs 6).toNat n sh M1 R3 hn1 hn4 hsh63 hdb hda1 hdisjd hMa0 (by rw [hTsp]; omega) (by rw [hTsp]; omega) ?kdn
    (n - 1) R3 fl3 M3 (Nat.le_refl _) hR3_6 r10 r11 r13 r12 (fun k hk => rfl) hfr3 (fun j h1 h2 => absurd h2 (by omega)) (fun j _ h2 => hz3 j h2)
  intro R4 fl4 M4 r10'' hRu4 hfr4 hdn4 hz4
  have hR4_6 : R4 6 = BitVec.ofNat 64 (s.regs 6).toNat := (hRu4 6 (by simp)).trans hR3_6
  have hR4_4 : R4 4 = BitVec.ofNat 64 L := (hRu4 4 (by simp)).trans hR3_4
  have hR4_9 : R4 9 = BitVec.ofNat 64 n := (hRu4 9 (by simp)).trans r9'
  have hR4_11 : R4 11 = BitVec.ofNat 64 sh := (hRu4 11 (by simp)).trans r11
  refine pro3 T _ _ (s.regs 6).toNat n sh L M1 M4 R4 fl4 hn1 hn4 hsh63 (by omega) hL8 hdb hda1 hMa0 hfr4 hdisjd hR4_6 hR4_9 hR4_11 hR4_4 hal
    (by rw [hTsp]; omega) (by rw [hTsp]; omega) ?kp3
  intro R5 fl5 Mdn r14 hRu5 hfr5 hdn0 hdnr
  -- the numerator length
  have hua5 : Mdn.accessible (s.regs 3).toNat (8 * L) false = true := by rw [hfr5.accessible, hfr1.accessible]; exact hua
  have hR5_3 : R5 3 = BitVec.ofNat 64 (s.regs 3).toNat := by
    rw [hRu5 3 (by simp), hRu4 3 (by simp), hRu3 3 (by simp), hRu2 3 (by simp), hRu1 3 (by simp)]; exact e3
  refine ulen_loop T _ _ (s.regs 3).toNat L Mdn R5 hub hua5 ?kul L R5 fl5 (Nat.le_refl _) hR5_3 r14 (fun k hk => rfl)
    (fun j h1 h2 => absurd h2 (by omega))
  intro R6 fl6 ulen r10u hule hz6 hnz6 hRu6
  have hR6_9 : R6 9 = BitVec.ofNat 64 n := by
    rw [hRu6 9 (by simp), hRu5 9 (by simp), hRu4 9 (by simp)]; exact r9'
  -- memory of the arrays is unchanged since the entry
  have hmemd : ∀ a, (a + 8 ≤ T.sp.toNat + 160 ∨ T.sp.toNat + 192 ≤ a) → (a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 216 ≤ a) →
      (a + 8 ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 16 ≤ a) → (a + 8 ≤ s.sp.toNat + 32 ∨ s.sp.toNat + 40 ≤ a) →
      Mdn.readLE a 8 = s.mem.readLE a 8 := fun a h1 h2 h3 h4 => by
    rw [hfr5.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hfr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
  have hudn : ∀ j, j < L → Mdn.readLE ((s.regs 3).toNat + 8 * j) 8 = s.mem.readLE ((s.regs 3).toNat + 8 * j) 8 := fun j hj =>
    hmemd _ (by rw [hTsp]; omega) (by omega) (by omega) (by omega)
  have uz : ∀ j, ulen ≤ j → j < L → s.mem.readLE ((s.regs 3).toNat + 8 * j) 8 = 0 := fun j h1 h2 => by
    rw [← hudn j h2]; exact hz6 j h1 h2
  have hdw : Fv256.B.wv s.mem (s.regs 6).toNat 4 = Fv256.B.wv s.mem (s.regs 6).toNat n := by
    rw [← hw1, Fv256.B.wv_ext M1 (s.regs 6).toNat n 4 (by omega) (fun j hj1 hj2 => hz j hj1 hj2)]
    exact Fv256.B.wv_of_frame s.mem M1 _ hfr1 _ n (by simp only [outside_cons, outside_nil, and_true]; have := hn4; omega)
  have hdt : s.mem.readLE ((s.regs 6).toNat + 8 * (n - 1)) 8 ≠ 0 := by
    rw [← hfr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; have := hn4; omega)]; exact hnz1
  have hx29t : Mdn.readLE (T.sp.toNat - 8) 8 = (s.regs 29).toNat := by
    rw [hfr5.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rw [show T.sp.toNat - 8 = s.sp.toNat - 232 by omega]; exact hx29m
  have hx30t : Mdn.readLE T.sp.toNat 8 = (s.regs 30).toNat := by
    rw [hfr5.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    rw [show T.sp.toNat = s.sp.toNat - 224 by omega]; exact hx30m
  have hfrS : MemFrame s.mem Mdn [(T.sp.toNat - 8, T.sp.toNat + 8), (T.sp.toNat + 160, T.sp.toNat + 192), (T.sp.toNat + 232, T.sp.toNat + 240), (T.sp.toNat + 256, T.sp.toNat + 264)] := by
    refine hfr1.trans hfr5 ?_
    intro a n' h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  have fin : ∀ (U : State) (R' : Nat → W64) (fl' : Flags) (Mf : Memory), U.sp = T.sp →
      FinOK L s.mem Mf (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat (s.regs 7).toNat (T.sp.toNat + 224) →
      R' 29 = BitVec.ofNat 64 (s.regs 29).toNat → R' 30 = BitVec.ofNat 64 (s.regs 30).toNat →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R' i = s.regs i) →
      UPost L s { U with regs := R', sp := U.sp + 224#64, pc := BitVec.ofNat 64 (s.regs 30).toNat, flags := fl', mem := Mf } := by
    intro U R' fl' Mf hU hF h29 h30 hR
    have hsp' : U.sp + 224#64 = s.sp := by rw [hU]; show s.sp - 224#64 + 224#64 = s.sp; bv_omega
    refine ⟨ofNat_toNat' _, hsp', hR 18 (by simp), hR 28 (by simp), h29.trans (ofNat_toNat' _), h30.trans (ofNat_toNat' _),
      fun i hi => ?_, ?_⟩
    · by_cases h29' : i = 29
      · subst h29'; exact h29.trans (ofNat_toNat' _)
      by_cases h30' : i = 30
      · subst h30'; exact h30.trans (ofNat_toNat' _)
      exact hR i (by simp at hi ⊢; omega)
    · have : T.sp.toNat + 224 = s.sp.toNat := by rw [hTsp]; omega
      rw [this] at hF; exact hF
  have hR6_3 : R6 3 = BitVec.ofNat 64 (s.regs 3).toNat := by
    rw [hRu6 3 (by simp)]; exact hR5_3
  have hR6_4 : R6 4 = BitVec.ofNat 64 L := by
    rw [hRu6 4 (by simp), hRu5 4 (by simp), hRu4 4 (by simp), hRu3 4 (by simp), hRu2 4 (by simp), hRu1 4 (by simp)]; exact hs4
  have hR6_7 : R6 7 = BitVec.ofNat 64 (s.regs 7).toNat := by
    rw [hRu6 7 (by simp), hRu5 7 (by simp), hRu4 7 (by simp), hRu3 7 (by simp), hRu2 7 (by simp), hRu1 7 (by simp)]; exact e7
  have hregs6 : ∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R6 i = s.regs i := fun i hi => by
    rw [hRu6 i (by simp at hi ⊢; omega), hRu5 i (by simp at hi ⊢; omega), hRu4 i (by simp at hi ⊢; omega), hRu3 i (by simp at hi ⊢; omega),
      hRu2 i (by simp at hi ⊢; omega), hRu1 i (by simp at hi ⊢; omega)]
  have hW : s.mem.accessible (T.sp.toNat - 120) 416 true = true := by
    rw [hTsp]; have := hsw; rw [show s.sp.toNat - 224 - 120 = s.sp.toNat - 344 by omega]; simpa using this
  rcases Nat.lt_or_ge ulen n with hlt | hge
  · refine ltjump T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) Mdn R6 fl6 n ulen hn4 (by omega) hlt hR6_9 r10u (fun fl' => ?_)
    refine UdivremC.caseL' T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) s.mem Mdn R6 fl' (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat (s.regs 7).toNat L n ulen
      (s.regs 29).toNat (s.regs 30).toNat hlt hn1 hn4 hdw hdt uz hfrS h30a h30b hal (by rw [hTsp]; omega) (by rw [hTsp]; omega) hL4 hL8
      hr64 hu64 hub hua (by rw [hTsp]; omega) hqb (by rw [hTsp]; omega) hq0 ?_ hW hR6_3 hR6_4 hR6_7 hx29t hx30t ?_
    · intro hr
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrem hr
      exact ⟨h1, h2, by rw [hTsp]; omega, by omega, by omega⟩
    · intro U R' fl'' Mf hU hF h29 h30 hR
      exact fin U R' fl'' Mf hU hF h29 h30 (fun i hi => (hR i (by simp at hi ⊢; omega)).trans (hregs6 i hi))
  · have hu1 : 1 ≤ ulen := by omega
    have hR6_13 : R6 13 = BitVec.ofNat 64 (sh + 64) := by
      rw [hRu6 13 (by simp), hRu5 13 (by simp), hRu4 13 (by simp)]; exact r13
    have hR6_11 : R6 11 = BitVec.ofNat 64 sh := by
      rw [hRu6 11 (by simp), hRu5 11 (by simp), hRu4 11 (by simp)]; exact r11
    have hMaS : Mdn.accessible T.sp.toNat 296 true = true := by rw [hfr5.accessible]; exact hMs1
    refine UdivremA.pro4 T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) (s.regs 3).toNat n ulen sh L Mdn R6 fl6 hn1 hn4 hsh63 hL8 hu1 (by omega) hub hua5 hal
      (by rw [hTsp]; omega) (by rw [hTsp]; omega) hMaS (by rw [hTsp]; omega) hR6_3 hR6_4 hR6_9 r10u hR6_11 hR6_13 hge ?kp4
    intro R7 fl7 M7 r14' r15' r16' r13' hRu7 hfr7 htopw hbelow habove
    have hub' : (s.regs 3).toNat + 8 * ulen ≤ 2 ^ 48 := by omega
    have hua7 : M7.accessible (s.regs 3).toNat (8 * ulen) false = true := by
      rw [hfr7.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hua5 (by omega) (by omega)
    have hMa7 : M7.accessible (T.sp.toNat + 80) 72 true = true := by
      rw [hfr7.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMaS (by omega) (by omega)
    have hR7_3 : R7 3 = BitVec.ofNat 64 (s.regs 3).toNat := by rw [hRu7 3 (by simp)]; exact hR6_3
    have hR7_11 : R7 11 = BitVec.ofNat 64 sh := by rw [hRu7 11 (by simp)]; exact hR6_11
    refine UdivremA.un_loop T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) (s.regs 3).toNat ulen sh M7 R7 hu1 (by omega) hsh63 hub' hua7
      (by rw [hTsp]; omega) hMa7 hal (by rw [hTsp]; omega) (by rw [hTsp]; omega) ?kun (ulen - 1) R7 fl7 M7 (Nat.le_refl _) hR7_3 r16' hR7_11 r13' r14'
      (fun k hk => rfl) (MemFrame.refl _ _) (fun j h1 h2 => absurd h2 (by omega)) (fun j _ _ => rfl)
    intro R8 fl8 M8 r16'' hRu8 hfr8 hdnun hzun
    have hMa8 : M7.accessible T.sp.toNat 296 true = true := by rw [hfr7.accessible]; exact hMaS
    have hR8_3 : R8 3 = BitVec.ofNat 64 (s.regs 3).toNat := by rw [hRu8 3 (by simp)]; exact hR7_3
    have hR8_7 : R8 7 = BitVec.ofNat 64 (s.regs 7).toNat := by rw [hRu8 7 (by simp), hRu7 7 (by simp)]; exact hR6_7
    have hR8_9 : R8 9 = BitVec.ofNat 64 n := by rw [hRu8 9 (by simp), hRu7 9 (by simp)]; exact hR6_9
    have hR8_11 : R8 11 = BitVec.ofNat 64 sh := by rw [hRu8 11 (by simp)]; exact hR7_11
    have hR8_5 : R8 5 = BitVec.ofNat 64 (n - 1) := by
      rw [hRu8 5 (by simp), hRu7 5 (by simp), hRu6 5 (by simp), hRu5 5 (by simp), hRu4 5 (by simp)]; exact r5'
    have hR8_13 : R8 13 = BitVec.ofNat 64 (64 - sh) := by rw [hRu8 13 (by simp)]; exact r13'
    have hR8_15 : R8 15 = BitVec.ofNat 64 (ulen + 1) := by rw [hRu8 15 (by simp)]; exact r15'
    have hR8_12 : R8 12 = BitVec.ofNat 64 (T.sp.toNat + 160) := by
      rw [hRu8 12 (by simp), hRu7 12 (by simp), hRu6 12 (by simp), hRu5 12 (by simp), hRu4 12 (by simp)]; exact r12
    have hR8_14 : R8 14 = BitVec.ofNat 64 (T.sp.toNat + 80) := by rw [hRu8 14 (by simp)]; exact r14'
    have hregs8 : ∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R8 i = s.regs i := fun i hi => by
      rw [hRu8 i (by simp at hi ⊢; omega), hRu7 i (by simp at hi ⊢; omega), hRu6 i (by simp at hi ⊢; omega), hRu5 i (by simp at hi ⊢; omega),
        hRu4 i (by simp at hi ⊢; omega), hRu3 i (by simp at hi ⊢; omega), hRu2 i (by simp at hi ⊢; omega), hRu1 i (by simp at hi ⊢; omega)]
    have hM1s : ∀ a, (a + 8 ≤ s.sp.toNat - 232 ∨ s.sp.toNat - 216 ≤ a) → (a + 8 ≤ s.sp.toNat + 8 ∨ s.sp.toNat + 16 ≤ a) →
        (a + 8 ≤ s.sp.toNat + 32 ∨ s.sp.toNat + 40 ≤ a) → M1.readLE a 8 = s.mem.readLE a 8 := fun a h1 h2 h3 =>
      hfr1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    have hdclz : sh = clzNat 64 (s.mem.readLE ((s.regs 6).toNat + 8 * (n - 1)) 8) := by
      rw [← hM1s _ (by omega) (by omega) (by omega)]; exact hshc
    have hdtB : s.mem.readLE ((s.regs 6).toNat + 8 * (n - 1)) 8 < 2 ^ 64 := by
      have := Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 6).toNat + 8 * (n - 1)) 8; simpa using this
    obtain ⟨_, hdc2, hdc3⟩ := Fv256.B.clz_norm _ hdt hdtB
    rw [← hdclz] at hdc2 hdc3
    have hdnw : ∀ k, k < n → Mdn.readLE (T.sp.toNat + 160 + 8 * k) 8 =
        (s.mem.readLE ((s.regs 6).toNat + 8 * k) 8 * 2 ^ sh) % 2 ^ 64 + Fv256.B.shc s.mem (s.regs 6).toNat sh k := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.mul_zero, Nat.add_zero, Fv256.B.shc, if_true]
        rw [hdn0, hM1s _ (by omega) (by omega) (by omega)]
      · rw [hdnr k (by omega), hdn4 k (by omega) hk]
        simp only [Fv256.B.shc, if_neg hk0]
        rw [hM1s _ (by rw [hTsp] at *; omega) (by omega) (by omega), hM1s _ (by omega) (by omega) (by omega)]
    have mkF : ∀ (M9 : Memory), MemFrame M8 M9 [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)] →
        M9.readLE (T.sp.toNat + 80) 8 = (M7.readLE (s.regs 3).toNat 8 * 2 ^ sh) % 2 ^ 64 →
        (∀ j, 1 ≤ j → j < 9 → M9.readLE (T.sp.toNat + 80 + 8 * j) 8 = M8.readLE (T.sp.toNat + 80 + 8 * j) 8) →
        (∀ j, j < n → M9.readLE (T.sp.toNat + 160 + 8 * j) 8 = M8.readLE (T.sp.toNat + 160 + 8 * j) 8) →
        M9.readLE (T.sp.toNat + 288) 8 = (s.regs 7).toNat → M9.readLE (T.sp.toNat + 208) 8 = sh →
        Front T.sp.toNat s.mem M9 (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat (s.regs 7).toNat L n ulen sh (s.regs 29).toNat (s.regs 30).toNat := by
      intro M9 hfr9 hun0 hunr hdn9 hrem9 hs9
      have hM7u : ∀ j, j < L → M7.readLE ((s.regs 3).toNat + 8 * j) 8 = s.mem.readLE ((s.regs 3).toNat + 8 * j) 8 := fun j hj => by
        rw [hfr7.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hudn j hj
      have hdnM : ∀ k, k < n → M9.readLE (T.sp.toNat + 160 + 8 * k) 8 = Mdn.readLE (T.sp.toNat + 160 + 8 * k) 8 := fun k hk => by
        rw [hdn9 k hk, hfr8.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          hfr7.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
      have hdnw9 : ∀ k, k < n → M9.readLE (T.sp.toNat + 160 + 8 * k) 8 =
          (s.mem.readLE ((s.regs 6).toNat + 8 * k) 8 * 2 ^ sh) % 2 ^ 64 + Fv256.B.shc s.mem (s.regs 6).toNat sh k := fun k hk => by
        rw [hdnM k hk]; exact hdnw k hk
      have hdnN := Fv256.B.dn_norm s.mem M9 (s.regs 6).toNat (T.sp.toNat + 160) n sh (s.mem.readLE ((s.regs 6).toNat + 8 * (n - 1)) 8) hn1 hsh63 rfl hdc2 hdc3 hdnw9
      have hunw9 : ∀ k, k < ulen → M9.readLE (T.sp.toNat + 80 + 8 * k) 8 =
          (s.mem.readLE ((s.regs 3).toNat + 8 * k) 8 * 2 ^ sh) % 2 ^ 64 + Fv256.B.shc s.mem (s.regs 3).toNat sh k := fun k hk => by
        by_cases hk0 : k = 0
        · subst hk0
          simp only [Nat.mul_zero, Nat.add_zero, Fv256.B.shc, if_true]
          rw [hun0]
          have := hM7u 0 (by omega)
          simp only [Nat.mul_zero, Nat.add_zero] at this
          rw [this]
        · rw [hunr k (by omega) (by omega), hdnun k (by omega) hk]
          simp only [Fv256.B.shc, if_neg hk0]
          rw [hM7u k (by omega), hM7u (k - 1) (by omega)]
      have hunt9 : M9.readLE (T.sp.toNat + 80 + 8 * ulen) 8 = s.mem.readLE ((s.regs 3).toNat + 8 * (ulen - 1)) 8 / 2 ^ (64 - sh) := by
        rw [hunr ulen hu1 (by omega), hzun ulen (Nat.le_refl _) (by omega), htopw]
        rw [hudn (ulen - 1) (by omega)]
      have hunN := Fv256.B.un_norm s.mem M9 (s.regs 3).toNat (T.sp.toNat + 80) ulen sh hu1 hsh63 hunw9 hunt9
      have hfrAll : MemFrame s.mem M9 [(T.sp.toNat - 8, T.sp.toNat + 8), (T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 232, T.sp.toNat + 240),
          (T.sp.toNat + 256, T.sp.toNat + 264), (T.sp.toNat + 288, T.sp.toNat + 296)] := by
        have h8' : MemFrame M7 M9 [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)] :=
          hfr8.trans hfr9 (rs'' := [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)])
            (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
        have h7' : MemFrame Mdn M9 [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)] :=
          hfr7.trans h8' (rs'' := [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)])
            (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
        exact hfrS.trans h7' (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      refine ⟨hn1, hn4, by omega, hge, hsh63, hdw, hdt, hdclz, Fv256.B.wv_ext s.mem (s.regs 3).toNat ulen L (by omega) uz,
        fun h => by rw [← hudn _ (by omega)]; exact hnz6 h, hdnN.1, hdnN.2, hunN, hfrAll, hrem9, hs9, ?_, ?_⟩
      · rw [hfr9.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          hfr8.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          hfr7.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hx29t
      · rw [hfr9.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          hfr8.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
          hfr7.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact hx30t
    refine UdivremA.pro5 T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) (s.regs 3).toNat n ulen sh L (s.regs 7).toNat M7 M8 R8 fl8 hn1 hn4 hsh63 hr64
      (by omega) hu1 hub' hua7 hal (by rw [hTsp]; omega) (by rw [hTsp]; omega) hMa8 hfr8 (by rw [hTsp]; omega) hR8_3 hR8_7 hR8_9 hR8_11 hR8_5
      hR8_13 hR8_15 hR8_12 hR8_14 ?hK1 ?hK2
    case hK1 =>
      intro hn1' R9 fl9 M9 hRu9 hfr9 hun0 hunr hrem9 hs9 hdn9
      subst hn1'
      have F := mkF M9 hfr9 hun0 hunr (fun j hj => by
        have : j = 0 := by omega
        subst this; simpa using hdn9) hrem9 hs9
      have hregs9 : ∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R9 i = s.regs i := fun i hi => by
        rw [hRu9 i (by simp at hi ⊢; omega)]; exact hregs8 i hi
      have hR9_28 : R9 28 = s.regs 28 := by rw [hRu9 28 (by simp)]; exact hregs8 28 (by simp)
      have hR9_0 : R9 0 = BitVec.ofNat 64 (s.regs 0).toNat := by
        rw [hRu9 0 (by simp), hRu8 0 (by simp), hRu7 0 (by simp), hRu6 0 (by simp), hRu5 0 (by simp), hRu4 0 (by simp), hRu3 0 (by simp),
          hRu2 0 (by simp), hRu1 0 (by simp)]; exact e0
      have hR9_1 : R9 1 = BitVec.ofNat 64 L := by
        rw [hRu9 1 (by simp), hRu8 1 (by simp), hRu7 1 (by simp), hRu6 1 (by simp), hRu5 1 (by simp), hRu4 1 (by simp), hRu3 1 (by simp),
          hRu2 1 (by simp), hRu1 1 (by simp)]; exact hs1
      have hR9_14 : R9 14 = BitVec.ofNat 64 (T.sp.toNat + 80) := by rw [hRu9 14 (by simp)]; exact hR8_14
      have hR9_15 : R9 15 = BitVec.ofNat 64 (ulen + 1) := by rw [hRu9 15 (by simp)]; exact hR8_15
      refine UdivremB.caseOne T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) s.mem M9 R9 fl9 (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat
        (s.regs 7).toNat L ulen sh (s.regs 29).toNat (s.regs 30).toNat F h30a h30b hal (by rw [hTsp]; omega) (by rw [hTsp]; omega) hW hL8 hqb hqa
        (by rw [hTsp]; omega) hq0 ?_ hr64 (by rw [hR9_28]; exact hg1) (by rw [hR9_28]; exact hg2) (by rw [hR9_28, hTsp]; omega)
        (by rw [hR9_28, hTsp]; omega) hR9_0 hR9_1 hR9_14 hR9_15 ?_
      · intro hr
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrem hr
        exact ⟨h1, h2, by rw [hTsp]; omega, h4⟩
      · intro U R' fl' Mf hU hF h29 h30 hR
        exact fin U R' fl' Mf hU hF h29 h30 (fun i hi => (hR i (by simp at hi ⊢; omega)).trans (hregs9 i hi))
    case hK2 =>
      intro hn1' R9 fl9 M9 r3'' r4'' r5'' r6'' r7'' r8'' hRu9 hfr9 hun0 hunr hrem9 hs9 hsn9 hsu9 hsc9 hdn9
      have F := mkF M9 hfr9 hun0 hunr (fun j hj => hdn9 j (by omega)) hrem9 hs9
      have hregs9 : ∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27, 29, 30] → R9 i = s.regs i := fun i hi => by
        rw [hRu9 i (by simp at hi ⊢; omega)]; exact hregs8 i hi
      have hR9_28 : R9 28 = s.regs 28 := by rw [hRu9 28 (by simp)]; exact hregs8 28 (by simp)
      have hR9_0 : R9 0 = BitVec.ofNat 64 (s.regs 0).toNat := by
        rw [hRu9 0 (by simp), hRu8 0 (by simp), hRu7 0 (by simp), hRu6 0 (by simp), hRu5 0 (by simp), hRu4 0 (by simp), hRu3 0 (by simp),
          hRu2 0 (by simp), hRu1 0 (by simp)]; exact e0
      have hR9_1 : R9 1 = BitVec.ofNat 64 L := by
        rw [hRu9 1 (by simp), hRu8 1 (by simp), hRu7 1 (by simp), hRu6 1 (by simp), hRu5 1 (by simp), hRu4 1 (by simp), hRu3 1 (by simp),
          hRu2 1 (by simp), hRu1 1 (by simp)]; exact hs1
      have hn2' : 2 ≤ n := by omega
      refine UdivremD.caseK hKn T (BitVec.ofNat 64 (s.regs 30).toNat) (UPost L s) s.mem M9 R9 fl9 (s.regs 0).toNat (s.regs 3).toNat (s.regs 6).toNat
        (s.regs 7).toNat L n ulen sh (s.regs 29).toNat (s.regs 30).toNat F hn2' h30a h30b hal (by rw [hTsp]; omega) (by rw [hTsp]; omega) hW hL8 hqb hqa
        (by rw [hTsp]; omega) hq0 ?_ hr64 (by rw [hR9_28]; exact hg1) (by rw [hR9_28]; exact hg2) (by rw [hR9_28, hTsp]; omega)
        (by rw [hR9_28, hTsp]; omega) hR9_0 hR9_1 r3'' r4'' r5'' r6'' r7'' r8'' F.s_x30 hsn9 hsu9 hsc9 ?_
      · intro hr
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrem hr
        exact ⟨h1, h2, by rw [hTsp]; omega, h4, h3⟩
      · intro U R' fl' Mf hU hF h29 h30 hR
        exact fin U R' fl' Mf hU hF h29 h30 (fun i hi => (hR i (by simp at hi ⊢; omega)).trans (hregs9 i hi))

end Fv256.Arm64.UdivremE
