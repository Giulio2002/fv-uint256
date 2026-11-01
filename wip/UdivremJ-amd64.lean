import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremB
import Fv256.Amd64.UdivremC
import Fv256.Amd64.UdivremD
import Fv256.Amd64.UdivremE
import Fv256.Amd64.UdivremF
import Fv256.Amd64.UdivremG
import Fv256.Amd64.UdivremH
import Fv256.Amd64.UdivremI

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA Fv256.Amd64.UdivremH Fv256.Amd64.UdivremI

namespace Fv256.Amd64.UdivremJ

set_option maxHeartbeats 32000000 in
theorem caseOne (s0 : State) (R : Nat → W64) (fl : Flags) (M M0 : Memory) (sp0 dp qp qcap ql up remp n ulen s rbpv ra : Nat)
    (F : Front R M M0 sp0 dp qp qcap ql up remp n ulen s rbpv ra) (hn1 : n = 1) (hge : n ≤ ulen) (g : W64) (hg : R 14 = g)
    (hql : ql = 4)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x48 ≤ 2 ^ 48) (hMs : M0.accessible (sp0 - 0x148) 0x190 true = true)
    (hup48 : up + 32 ≤ 2 ^ 48) (hua : M0.accessible up 32 false = true) (hdisju : up + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ up)
    (hdp : dp + 32 ≤ 2 ^ 48) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ dp)
    (hq48 : qp + 32 ≤ 2 ^ 48) (hqa : M0.accessible qp 32 true = true) (hq0 : Fv256.B.wv M0 qp 4 = 0) (hqs : qp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ qp)
    (hremB : remp < 2 ^ 64)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ Fv256.B.wv M0 remp 4 = 0)
    (hqr : remp ≠ 0 → qp + 32 ≤ remp ∨ remp + 32 ≤ qp) (hru : remp ≠ 0 → remp + 32 ≤ up ∨ up + 32 ≤ remp)
    (hrs : remp ≠ 0 → remp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ remp) (hra47 : ra < 2 ^ 47) (hx15 : s0.xmm 15 = 0)
    (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M0.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M0.readLE ((R 14).toNat + 16) 8 < sp0 - 0xf8) (hgd : (R 14).toNat + 24 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ (R 14).toNat + 16) :
    ReachesRet Extracted.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (UPost s0 M0 sp0 dp qp up remp ra rbpv g) := by
  have hcode := ku_lt
  obtain ⟨hn, hn4, hul4, hs63⟩ : 1 ≤ n ∧ n ≤ 4 ∧ ulen ≤ 4 ∧ s ≤ 63 := ⟨F.hn, F.hn4, F.hulen, F.hs⟩
  have hfr := F.frame
  have hua1 : M.accessible up 32 false = true := by rw [hfr.accessible]; exact hua
  have hMs1 : M.accessible (sp0 - 0xf0) 0x138 true = true := by
    rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have h1 := Fv256.Amd64.UdivremD.mid2 s0 dp qp qcap ql up remp n 4 ulen s (sp0 - 0xf0) R fl M hs63 hn4 hn rfl hul4 hge hup48 hua1
    (by omega) hMs1 (by omega) (by omega) hx15 F.e12 F.e0 F.e1 F.e3 F.e7 F.e10 F.e11 F.e8 F.e13 F.e15 F.e9 F.e4 F.e2 F.e6
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 _ ⟨R1, fl1, M1, hS1, a0, a1, a2, a10, a13, ak, sb8, sz, stop, fr1⟩
  subst hS1
  have hua2 : M1.accessible up 32 false = true := by rw [fr1.accessible]; exact hua1
  have hMs2 : M1.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr1.accessible]; exact hMs1
  have h2 := Fv256.Amd64.UdivremD.un_loop s0 up ulen s (sp0 - 0xf0) hs63 hul4 hup48 (by omega) (by omega) (by omega) (ulen - 1) (by omega)
    R1 fl1 M1 hua2 hMs2 (by rw [a0]) ((ak 7 (by simp)).trans F.e7) ((ak 11 (by simp)).trans F.e11) ((ak 8 (by simp)).trans F.e8) a13
    ((ak 15 (by simp)).trans F.e15) a2 ((ak 4 (by simp)).trans F.e4) (fun k hk1 hk2 => by omega)
  refine Fv256.B.reachesRet_trans64 h2 ?_
  intro S2 _ ⟨R2, fl2, M2, hS2, b0, bk, bmem, fr2⟩
  subst hS2
  have bk1 : ∀ k, k ∉ [0, 1, 6, 12] → R2 k = R1 k := fun k hk => by
    have : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 6 ∧ k ≠ 12 := by simp at hk; omega
    exact bk k this.1 this.2.1 this.2.2.1 this.2.2.2
  have hua3 : M2.accessible up 32 false = true := by rw [fr2.accessible]; exact hua2
  have hMs3 : M2.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr2.accessible]; exact hMs2
  have hsb8 : M2.readLE (sp0 - 0xf0 + 0xb8) 8 = n := by
    rw [fr2.readLE _ _ (by simp [Outside] <;> omega)]; exact sb8
  have h3 := Fv256.Amd64.UdivremD.midA1 s0 up n ulen s (sp0 - 0xf0) R2 fl2 M2 hs63 hul4 hn1 hup48 hua3 (by omega) hMs3 (by omega) (by omega) hx15
    ((bk1 7 (by simp)).trans ((ak 7 (by simp)).trans F.e7)) ((bk1 11 (by simp)).trans ((ak 11 (by simp)).trans F.e11))
    ((bk1 15 (by simp)).trans ((ak 15 (by simp)).trans F.e15)) ((bk1 4 (by simp)).trans ((ak 4 (by simp)).trans F.e4)) hsb8
  refine Fv256.B.reachesRet_trans64 h3 ?_
  intro S3 _ ⟨R3, fl3, M3, hS3, c12, ck, cd8, cd0, c48, fr3⟩
  subst hS3
  -- memory facts at the call
  have fr13 : MemFrame M M3 [(sp0 - 0xf0 + 0xb8, sp0 - 0xf0 + 0xc0), (sp0 - 0xf0 + 0x48, sp0 - 0xf0 + 0x90), (sp0 - 0xf0 + 0xd0, sp0 - 0xf0 + 0xe0)] := by
    have a12' : MemFrame M M2 [(sp0 - 0xf0 + 0xb8, sp0 - 0xf0 + 0xc0), (sp0 - 0xf0 + 0x48, sp0 - 0xf0 + 0x90), (sp0 - 0xf0 + 0xd0, sp0 - 0xf0 + 0xe0)] :=
      fr1.trans fr2 (by intro a n' h; simp [Outside] at h ⊢; omega)
    exact a12'.trans fr3 (by intro a n' h; simp [Outside] at h ⊢; omega)
  have hq3 : M3.accessible qp 32 true = true := by rw [fr13.accessible, hfr.accessible]; exact hqa
  have hMs4 : M3.accessible (sp0 - 0xf0 - 0x58) 0x190 true = true := by
    rw [fr13.accessible, hfr.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have hg3' : M3.readLE ((R 14).toNat + 16) 8 < sp0 - 0xf0 - 8 := by
    rw [fr13.readLE _ _ (by simp [Outside] <;> omega), hfr.readLE _ _ (by simp [Outside] <;> omega)]; omega
  have hg23 : M3.accessible ((R 14).toNat + 16) 8 false = true := by
    rw [fr13.accessible, hfr.accessible]; exact hg2
  have hdn3 : Fv256.B.wv M3 (sp0 - 0xf0 + 0x98) n = Fv256.B.wv M (sp0 - 0xf0 + 0x98) n :=
    Fv256.B.wv_of_frame M M3 _ fr13 _ _ (by simp [Outside]; omega)
  have hdntop3 : 2 ^ 63 ≤ M3.readLE (sp0 - 0xf0 + 0x98 + 8 * (n - 1)) 8 := by
    rw [fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.dntop
  have hsf8 : M3.readLE (sp0 - 0xf0 + 0xf8) 8 = qp := by
    rw [fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.s_f8
  have hu1 : ∀ j, j ≤ 3 → M1.readLE (up + 8 * j) 8 = M.readLE (up + 8 * j) 8 := fun j hj =>
    fr1.readLE _ _ (by simp [Outside]; omega)
  have hu2 : ∀ j, j ≤ 3 → M2.readLE (up + 8 * j) 8 = M.readLE (up + 8 * j) 8 := fun j hj =>
    (fr2.readLE _ _ (by simp [Outside]; omega)).trans (hu1 j hj)
  have hun : ∀ k, k < ulen → M3.readLE (sp0 - 0xf0 + 0x48 + 8 * k) 8 =
      (M.readLE (up + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + Fv256.B.shc M up s k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp only [Nat.mul_zero, Nat.add_zero, Fv256.B.shc, if_true]
      have h20 := hu2 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at h20
      rw [c48, h20]
    · unfold Fv256.B.shc
      rw [if_neg (by omega)]
      rw [fr3.readLE _ _ (by simp [Outside] <;> omega), bmem k h0 hk, hu1 k (by omega), hu1 (k - 1) (by omega)]
  have htop : M3.readLE (sp0 - 0xf0 + 0x48 + 8 * ulen) 8 = M.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - s) := by
    rw [fr3.readLE _ _ (by simp [Outside] <;> omega), fr2.readLE _ _ (by simp [Outside] <;> omega), stop]
  have hUn := Fv256.B.un_norm M M3 up (sp0 - 0xf0 + 0x48) ulen s (by omega) hs63 hun htop
  have hUlt := Fv256.B.wv_lt M up ulen
  have hDn : Fv256.B.wv M3 (sp0 - 0xf0 + 0x98) n = Fv256.B.wv M dp n * 2 ^ s := hdn3.trans F.dn
  have hDb : 2 ^ 63 * 2 ^ (64 * (n - 1)) ≤ Fv256.B.wv M3 (sp0 - 0xf0 + 0x98) n := by
    have h1 := Fv256.B.wv_ge_top M3 (sp0 - 0xf0 + 0x98) n hn
    have h2 := Nat.mul_le_mul_right (2 ^ (64 * (n - 1))) hdntop3
    omega
  have hD := Fv256.B.knuth_pre_lt M3 (sp0 - 0xf0 + 0x48) ulen n s _ _ hn hge hs63 hUlt hUn hDb
  have hR3_14 : R3 14 = R 14 := (ck 14 (by simp)).trans ((bk1 14 (by simp)).trans (ak 14 (by simp)))
  have hg23' : M3.accessible ((R3 14).toNat + 16) 8 false = true := by rw [hR3_14]; exact hg23
  have hg3'' : M3.readLE ((R3 14).toNat + 16) 8 < sp0 - 0xf0 - 8 := by rw [hR3_14]; exact hg3'

  have hd0w : Fv256.B.wv M3 (sp0 - 0xf0 + 0x98) 1 = M3.readLE (sp0 - 0xf0 + 0x98) 8 := by simp [Fv256.B.wv]
  have hD1 : M3.readLE (sp0 - 0xf0 + 72 + 8 * ulen) 8 < M3.readLE (sp0 - 0xf0 + 0x98) 8 := by
    subst hn1
    have h := hD
    simp only [Fv256.B.wv, Nat.mul_zero, Nat.add_zero, Nat.mul_zero] at h
    rw [show sp0 - 0xf0 + 0x48 + 8 * (ulen + 1 - 1) = sp0 - 0xf0 + 72 + 8 * ulen by omega] at h
    omega
  have hd0lt : M3.readLE (sp0 - 0xf0 + 0x98) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M3 (sp0 - 0xf0 + 0x98) 8; simpa using this
  have hdt1 : 2 ^ 63 ≤ M3.readLE (sp0 - 0xf0 + 0x98) 8 := by
    have := hdntop3; subst hn1; simpa using this
  have h4 := Fv256.Amd64.UdivremE.midB1 s0 qp qcap ql ulen s (sp0 - 0xf0) _ R3 fl3 M3 hs63 hul4 (by omega) hql (by omega) (by omega) hMs4
    (by omega) hq3 (by omega) hx15 (by rw [hR3_14]; exact hg1) hg23' hg3'' (by rw [hR3_14]; omega)
    ((ck 2 (by simp)).trans ((bk1 2 (by simp)).trans a2))
    ((ck 3 (by simp)).trans ((bk1 3 (by simp)).trans ((ak 3 (by simp)).trans F.e3)))
    ((ck 10 (by simp)).trans ((bk1 10 (by simp)).trans a10))
    ((ck 9 (by simp)).trans ((bk1 9 (by simp)).trans ((ak 9 (by simp)).trans F.e9)))
    ((ck 4 (by simp)).trans ((bk1 4 (by simp)).trans ((ak 4 (by simp)).trans F.e4)))
    hsf8 rfl hd0lt hdt1 hD1
  refine Fv256.B.reachesRet_trans64 h4 ?_
  intro S4 _ ⟨R4, fl4, M4, rr, hS4, d0, d4, d14, hrr, hwv, fr4⟩
  subst hS4
  have hDpos : 0 < Fv256.B.wv M dp n := by
    have h1 := Fv256.B.wv_ge_top M dp n hn
    have h3 : 1 ≤ M.readLE (dp + 8 * (n - 1)) 8 := Nat.pos_of_ne_zero F.dtop
    have h5 : 2 ^ (64 * (n - 1)) ≤ M.readLE (dp + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) := Nat.le_mul_of_pos_left _ h3
    have h6 : 0 < 2 ^ (64 * (n - 1)) := Nat.two_pow_pos _
    omega
  have hDn1 : M3.readLE (sp0 - 0xf0 + 0x98) 8 = Fv256.B.wv M dp n * 2 ^ s := by rw [← hd0w]; subst hn1; exact hDn
  have hdiv := Fv256.B.norm_div_eq (Fv256.B.wv M up ulen) (Fv256.B.wv M dp n) (2 ^ s) (Fv256.B.wv M4 qp ulen) rr (Nat.two_pow_pos _) hDpos
    (by rw [← hUn, hwv, hDn1]) (by rw [← hDn1]; exact hrr)
  have hUD : Fv256.B.wv M0 up 4 = Fv256.B.wv M up ulen := by
    rw [← F.uwv]; exact (Fv256.B.wv_of_frame M0 M _ hfr up 4 (by simp [Outside]; omega)).symm
  have hDD : Fv256.B.wv M0 dp 4 = Fv256.B.wv M dp n := by
    rw [← F.dwv]; exact (Fv256.B.wv_of_frame M0 M _ hfr dp 4 (by simp [Outside]; omega)).symm
  have hqw : ∀ j, j < 4 → M0.readLE (qp + 8 * j) 8 = 0 := Fv256.B.wv_zero_word M0 qp 4 hq0
  have hq4 : Fv256.B.wv M4 qp 4 = Fv256.B.wv M4 qp ulen := by
    refine Fv256.B.wv_ext M4 qp ulen 4 hul4 (fun j hj1 hj2 => ?_)
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), hfr.readLE _ _ (by simp [Outside] <;> omega)]
    exact hqw j hj2
  have hQ : Fv256.B.wv M4 qp 4 = Fv256.B.wv M0 up 4 / Fv256.B.wv M0 dp 4 := by
    rw [hq4, hdiv.1, hUD, hDD]
  have hsfx : sp0 - 0xf0 + 0x138 ≤ 2 ^ 48 := by omega
  have frx : MemFrame M0 M4 [(qp, qp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] := by
    have a1 : MemFrame M0 M3 [(qp, qp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] :=
      hfr.trans fr13 (by intro a n' h; simp [Outside] at h ⊢; omega)
    exact a1.trans fr4 (by intro a n' h; simp [Outside] at h ⊢; omega)
  have hMs5 : M4.accessible (sp0 - 0xf0) 0x138 true = true := by
    rw [fr4.accessible, fr13.accessible, hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have hMs6 : M4.accessible (sp0 - 0xf0) 0xf8 true = true := Janus.Arm64.Memory.accessible_mono _ hMs5 (by omega) (by omega)
  have se8 : M4.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), show sp0 - 0xf0 + 0xe8 = sp0 - 8 by omega]
    exact F.s_e8
  have sf0 : M4.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), show sp0 - 0xf0 + 0xf0 = sp0 by omega]
    exact F.s_f0
  have m130 : M4.readLE (sp0 - 0xf0 + 0x130) 8 = remp := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.s_130
  have hR414 : R4 14 = g := d14.trans (hR3_14.trans hg)
  by_cases hr0 : remp = 0
  · subst hr0
    have m130' : M4.readLE (sp0 - 0xf0 + 0x130) 8 = 0 := m130
    have h5 := Fv256.Amd64.UdivremF.by1_tail_nil s0 (sp0 - 0xf0) R4 fl4 M4 hsfx hMs5 (by omega) d4 m130'
    refine Fv256.B.reachesRet_trans64 h5 ?_
    intro S5 _ ⟨R5, fl5, hS5, k5⟩
    subst hS5
    have h6 := Fv256.Amd64.UdivremF.epilogue2 s0 (sp0 - 0xf0) rbpv ra R5 fl5 M4 (by omega) (by omega) hMs6 ((k5 4 (by simp)).trans d4) se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h6 ?_
    rintro S ⟨R6, fl6, hS6, h64, h65, h614⟩
    refine ⟨R6, fl6, s0.xmm, M4, by rw [hS6], ?_, h65, ?_, rfl, hQ, ?_, ?_⟩
    · rw [h64, sp_arith sp0 hsp0]
    · rw [h614, k5 14 (by simp), hR414]
    · intro h; exact absurd rfl h
    · exact frx.mono (by intro a n' h; simp [Outside] at h ⊢; omega)
  · obtain ⟨hr48, hra, hr0z⟩ := hrem hr0
    have hrs' := hrs hr0
    have hqr' := hqr hr0
    have hra4 : M4.accessible remp 32 true = true := by
      rw [fr4.accessible, fr13.accessible, hfr.accessible]; exact hra
    have md0 : M4.readLE (sp0 - 0xf0 + 0xd0) 8 = 18446744073709551615 := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega)]; exact cd0
    have md8 : M4.readLE (sp0 - 0xf0 + 0xd8) 8 = 18446744073709551616 - (64 - s) := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega)]; exact cd8
    have hrr64 : rr < 2 ^ 64 := Nat.lt_trans hrr hd0lt
    have hdsj : remp + 32 ≤ sp0 - 0xf0 ∨ sp0 - 0xf0 + 0x138 ≤ remp := by omega
    have h5 := Fv256.Amd64.UdivremF.by1_tail_ne s0 remp rr s (sp0 - 0xf0) R4 fl4 M4 hs63 hr0 hremB hrr64 hr48 hra4 hsfx hMs5 (by omega) hdsj hx15
      d0 d4 m130 md0 md8
    refine Fv256.B.reachesRet_trans64 h5 ?_
    intro S5 _ ⟨R5, fl5, M5, hS5, g4, gk, w0, w1, w2, w3, gfr⟩
    subst hS5
    have hMs7 : M5.accessible (sp0 - 0xf0) 0xf8 true = true := by rw [gfr.accessible]; exact hMs6
    have se8' : M5.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by
      rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact se8
    have sf0' : M5.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by
      rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sf0
    have hrv : Fv256.B.wv M5 remp 4 = Fv256.B.wv M0 up 4 % Fv256.B.wv M0 dp 4 := by
      rw [Fv256.B.wv_ext M5 remp 1 4 (by omega) (fun j h1 h2 => ?_)]
      · have e1 : Fv256.B.wv M5 remp 1 = M5.readLE remp 8 := by simp [Fv256.B.wv]
        rw [e1, w0, hdiv.2, Nat.mul_div_cancel _ (Nat.two_pow_pos s), hUD, hDD]
      · have : j = 1 ∨ j = 2 ∨ j = 3 := by omega
        rcases this with rfl | rfl | rfl
        · simpa using w1
        · simpa using w2
        · simpa using w3
    have fr5 : MemFrame M0 M5 [(qp, qp + 32), (remp, remp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] :=
      frx.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)
    have hq5 : Fv256.B.wv M5 qp 4 = Fv256.B.wv M4 qp 4 :=
      Fv256.B.wv_of_frame M4 M5 _ gfr qp 4 (by simp [Outside]; omega)
    have h8 := Fv256.Amd64.UdivremF.epilogue2 s0 (sp0 - 0xf0) rbpv ra R5 fl5 M5 (by omega) (by omega) hMs7 g4 se8' sf0' hra47
    refine Fv256.B.reachesRet_mono64 h8 ?_
    rintro S ⟨R8, fl8, hS8, h84, h85, h814⟩
    refine ⟨R8, fl8, s0.xmm, M5, by rw [hS8], ?_, h85, ?_, rfl, ?_, fun _ => hrv, fr5⟩
    · rw [h84, sp_arith sp0 hsp0]
    · rw [h814, gk 14 (by simp), hR414]
    · rw [hq5]; exact hQ

end Fv256.Amd64.UdivremJ
