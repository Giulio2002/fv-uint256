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

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA Fv256.Amd64.UdivremH

namespace Fv256.Amd64.UdivremI

/-- What `udivrem` guarantees on return. -/
def UPost (L : Nat) (s0 : State) (M0 : Memory) (sp0 dp qp up remp ra rbpv : Nat) (g : W64) (S' : State) : Prop :=
  ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory),
    S' = { s0 with regs := R', rip := BitVec.ofNat 64 ra, flags := fl', xmm := X', mem := M' } ∧
    R' 4 = BitVec.ofNat 64 (sp0 + 8) ∧ R' 5 = BitVec.ofNat 64 rbpv ∧ R' 14 = g ∧ X' 15 = s0.xmm 15 ∧
    Fv256.B.wv M' qp L = Fv256.B.wv M0 up L / Fv256.B.wv M0 dp 4 ∧
    (remp ≠ 0 → Fv256.B.wv M' remp 4 = Fv256.B.wv M0 up L % Fv256.B.wv M0 dp 4) ∧
    (remp = 0 → MemFrame M0 M' [(qp, qp + 8 * L), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)]) ∧
    (remp ≠ 0 → MemFrame M0 M' [(qp, qp + 8 * L), (remp, remp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)])

theorem sp_arith (sp0 : Nat) (h : 0x150 ≤ sp0) : sp0 - 0xf0 + 0xf8 = sp0 + 8 := by omega

set_option maxHeartbeats 16000000 in
theorem caseL {L : Nat} (hL : L ≤ 8) (s0 : State) (R : Nat → W64) (fl : Flags) (M M0 : Memory) (sp0 dp qp qcap ql up remp n ulen s rbpv ra : Nat)
    (F : Front L R M M0 sp0 dp qp qcap ql up remp n ulen s rbpv ra) (hlt : ulen < n) (g : W64) (hg : R 14 = g)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x48 ≤ 2 ^ 48) (hMs : M0.accessible (sp0 - 0x148) 0x190 true = true)
    (hup48 : up + 8 * L ≤ 2 ^ 48) (hua : M0.accessible up (8 * L) false = true) (hdisju : up + 8 * L ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ up)
    (hdp : dp + 32 ≤ 2 ^ 48) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ dp)
    (hq48 : qp + 8 * L ≤ 2 ^ 48) (hq0 : Fv256.B.wv M0 qp L = 0) (hqs : qp + 8 * L ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ qp)
    (hremB : remp < 2 ^ 64)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ Fv256.B.wv M0 remp 4 = 0)
    (hqr : remp ≠ 0 → qp + 8 * L ≤ remp ∨ remp + 32 ≤ qp) (hru : remp ≠ 0 → remp + 32 ≤ up ∨ up + 8 * L ≤ remp)
    (hrs : remp ≠ 0 → remp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ remp) (hra47 : ra < 2 ^ 47) (hx15 : s0.xmm 15 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (UPost L s0 M0 sp0 dp qp up remp ra rbpv g) := by
  have hcode := ku_lt
  obtain ⟨hn, hn4, hul4, hs63⟩ : 1 ≤ n ∧ n ≤ 4 ∧ ulen ≤ L ∧ s ≤ 63 := ⟨F.hn, F.hn4, F.hulen, F.hs⟩
  have hfr := F.frame
  have hUw : Fv256.B.wv M0 up L = Fv256.B.wv M up L := (Fv256.B.wv_of_frame M0 M _ hfr up L (by simp [Outside]; omega)).symm
  have hDw : Fv256.B.wv M0 dp 4 = Fv256.B.wv M dp 4 := (Fv256.B.wv_of_frame M0 M _ hfr dp 4 (by simp [Outside]; omega)).symm
  have hUlt : Fv256.B.wv M0 up L < Fv256.B.wv M0 dp 4 := by
    rw [hUw, hDw, F.uwv, F.dwv]
    have h1 := Fv256.B.wv_lt M up ulen
    have h2 := Fv256.B.wv_ge_top M dp n hn
    have h3 : 1 ≤ M.readLE (dp + 8 * (n - 1)) 8 := Nat.pos_of_ne_zero F.dtop
    have h4 : 2 ^ (64 * ulen) ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    have h5 : 2 ^ (64 * (n - 1)) ≤ M.readLE (dp + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) := Nat.le_mul_of_pos_left _ h3
    omega
  have hqM : Fv256.B.wv M qp L = 0 := by
    rw [← hq0]; exact Fv256.B.wv_of_frame M0 M _ hfr qp L (by simp [Outside]; omega)
  have hsf : sp0 - 0xf0 + 0xf8 ≤ 2 ^ 48 := by omega
  have hMs' : M.accessible (sp0 - 0xf0) 0xf8 true = true := by
    rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have se8 : M.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by rw [show sp0 - 0xf0 + 0xe8 = sp0 - 8 by omega]; exact F.s_e8
  have sf0 : M.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by rw [show sp0 - 0xf0 + 0xf0 = sp0 by omega]; exact F.s_f0
  by_cases hr0 : remp = 0
  · subst hr0
    have h1 := Fv256.Amd64.UdivremG.ulen_lt_nil s0 n ulen (sp0 - 0xf0) ra rbpv R fl M hn4 hlt hsf (by omega) hMs' F.e12 F.e2
      (by simpa using F.e10) F.e4 se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h1 ?_
    rintro S ⟨R', fl', hS, h4, h5, h14⟩
    refine ⟨R', fl', s0.xmm, M, by rw [hS], ?_, h5, ?_, rfl, ?_, ?_, ?_⟩
    · rw [h4, sp_arith sp0 hsp0]
    · rw [h14, hg]
    · rw [hqM, Nat.div_eq_of_lt hUlt]
    · intro h; exact absurd rfl h
    · exact ⟨fun _ => hfr.mono (by intro a n' h; simp [Outside] at h ⊢; omega), fun h => absurd rfl h⟩
  · obtain ⟨hr48, hra, hr0z⟩ := hrem hr0
    have hua' : M.accessible up (8 * L) false = true := by rw [hfr.accessible]; exact hua
    have hra' : M.accessible remp 32 true = true := by rw [hfr.accessible]; exact hra
    have hMs2 : M.accessible (sp0 - 0xf0 - 0x58) 0x150 true = true := by
      rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
    have h1 := Fv256.Amd64.UdivremG.ulen_lt_ne hL s0 up remp n ulen (sp0 - 0xf0) ra rbpv R fl M hn4 hlt hr0 hremB hup48 hua' hr48 hra'
      (by have := hru hr0; omega) hsf (by omega) hMs2 (by omega) (by have := hrs hr0; omega) F.e12 F.e2 F.e6 F.e7 F.e10 F.e4 se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h1 ?_
    rintro S ⟨R', fl', X', M', hS, h4, h5, hx, h14, hcp, hf'⟩
    refine ⟨R', fl', X', M', by rw [hS], ?_, h5, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h4, sp_arith sp0 hsp0]
    · rw [h14, hg]
    · rw [hx, hx15]
    · have hq' : Fv256.B.wv M' qp L = Fv256.B.wv M qp L := Fv256.B.wv_of_frame M M' _ hf' qp L (by have := hqr hr0; simp [Outside]; omega)
      rw [hq', hqM, Nat.div_eq_of_lt hUlt]
    · intro _
      rw [Nat.mod_eq_of_lt hUlt, hUw]
      exact Fv256.B.wv_congr M' M remp up L (fun j hj => hcp j hj)
    · exact ⟨fun h => absurd h hr0, fun _ => hfr.trans hf' (by intro a n' h; simp [Outside] at h ⊢; omega)⟩

set_option maxHeartbeats 32000000 in
theorem caseK {L : Nat} (hL : L ≤ 8) (s0 : State) (R : Nat → W64) (fl : Flags) (M M0 : Memory) (sp0 dp qp qcap ql up remp n ulen s rbpv ra : Nat)
    (F : Front L R M M0 sp0 dp qp qcap ql up remp n ulen s rbpv ra) (hn2 : 2 ≤ n) (hge : n ≤ ulen) (g : W64) (hg : R 14 = g)
    (hql : ql = L)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x48 ≤ 2 ^ 48) (hMs : M0.accessible (sp0 - 0x148) 0x190 true = true)
    (hup48 : up + 8 * L ≤ 2 ^ 48) (hua : M0.accessible up (8 * L) false = true) (hdisju : up + 8 * L ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ up)
    (hdp : dp + 32 ≤ 2 ^ 48) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ dp)
    (hq48 : qp + 8 * L ≤ 2 ^ 48) (hqa : M0.accessible qp (8 * L) true = true) (hq0 : Fv256.B.wv M0 qp L = 0) (hqs : qp + 8 * L ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ qp)
    (hremB : remp < 2 ^ 64)
    (hrem : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ M0.accessible remp 32 true = true ∧ Fv256.B.wv M0 remp 4 = 0)
    (hqr : remp ≠ 0 → qp + 8 * L ≤ remp ∨ remp + 32 ≤ qp) (hru : remp ≠ 0 → remp + 32 ≤ up ∨ up + 8 * L ≤ remp)
    (hrs : remp ≠ 0 → remp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ remp) (hra47 : ra < 2 ^ 47) (hx15 : s0.xmm 15 = 0)
    (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M0.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M0.readLE ((R 14).toNat + 16) 8 < sp0 - 0xf8) (hgd : (R 14).toNat + 24 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ (R 14).toNat + 16) :
    ReachesRet Extracted.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (UPost L s0 M0 sp0 dp qp up remp ra rbpv g) := by
  have hcode := ku_lt
  obtain ⟨hn, hn4, hul4, hs63⟩ : 1 ≤ n ∧ n ≤ 4 ∧ ulen ≤ L ∧ s ≤ 63 := ⟨F.hn, F.hn4, F.hulen, F.hs⟩
  have hfr := F.frame
  have hua1 : M.accessible up (8 * L) false = true := by rw [hfr.accessible]; exact hua
  have hMs1 : M.accessible (sp0 - 0xf0) 0x138 true = true := by
    rw [hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have h1 := Fv256.Amd64.UdivremD.mid2 hL s0 dp qp qcap ql up remp n L ulen s (sp0 - 0xf0) R fl M hs63 hn4 hn rfl hul4 hge hup48 hua1
    (by omega) hMs1 (by omega) (by omega) hx15 F.e12 F.e0 F.e1 F.e3 F.e7 F.e10 F.e11 F.e8 F.e13 F.e15 F.e9 F.e4 F.e2 F.e6
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 _ ⟨R1, fl1, M1, hS1, a0, a1, a2, a10, a13, ak, sb8, sz, stop, fr1⟩
  subst hS1
  have hua2 : M1.accessible up (8 * L) false = true := by rw [fr1.accessible]; exact hua1
  have hMs2 : M1.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr1.accessible]; exact hMs1
  have h2 := Fv256.Amd64.UdivremD.un_loop hL s0 up ulen s (sp0 - 0xf0) hs63 hul4 hup48 (by omega) (by omega) (by omega) (ulen - 1) (by omega)
    R1 fl1 M1 hua2 hMs2 (by rw [a0]) ((ak 7 (by simp)).trans F.e7) ((ak 11 (by simp)).trans F.e11) ((ak 8 (by simp)).trans F.e8) a13
    ((ak 15 (by simp)).trans F.e15) a2 ((ak 4 (by simp)).trans F.e4) (fun k hk1 hk2 => by omega)
  refine Fv256.B.reachesRet_trans64 h2 ?_
  intro S2 _ ⟨R2, fl2, M2, hS2, b0, bk, bmem, fr2⟩
  subst hS2
  have bk1 : ∀ k, k ∉ [0, 1, 6, 12] → R2 k = R1 k := fun k hk => by
    have : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 6 ∧ k ≠ 12 := by simp at hk; omega
    exact bk k this.1 this.2.1 this.2.2.1 this.2.2.2
  have hua3 : M2.accessible up (8 * L) false = true := by rw [fr2.accessible]; exact hua2
  have hMs3 : M2.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr2.accessible]; exact hMs2
  have hsb8 : M2.readLE (sp0 - 0xf0 + 0xb8) 8 = n := by
    rw [fr2.readLE _ _ (by simp [Outside] <;> omega)]; exact sb8
  have h3 := Fv256.Amd64.UdivremD.midA hL s0 up n ulen s (sp0 - 0xf0) R2 fl2 M2 hs63 hul4 hn2 hn4 hup48 hua3 (by omega) hMs3 (by omega) (by omega) hx15
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
  have hq3 : M3.accessible qp (8 * L) true = true := by rw [fr13.accessible, hfr.accessible]; exact hqa
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
  have hrb : 0 < sp0 - 0xf0 - 8 := by omega
  have h4 := Fv256.Amd64.UdivremE.midB hL s0 qp qcap ql ulen n s (sp0 - 0xf0) R3 fl3 M3 hs63 hn4 hn2 hul4 hge hql (by omega) (by omega) hMs4
    (by omega) hq3 (by omega) hx15 (by rw [hR3_14]; exact hg1) hg23' hg3'' (by rw [hR3_14]; omega)
    ((ck 2 (by simp)).trans ((bk1 2 (by simp)).trans a2))
    ((ck 3 (by simp)).trans ((bk1 3 (by simp)).trans ((ak 3 (by simp)).trans F.e3)))
    ((ck 10 (by simp)).trans ((bk1 10 (by simp)).trans a10)) c12
    ((ck 8 (by simp)).trans ((bk1 8 (by simp)).trans ((ak 8 (by simp)).trans F.e8)))
    ((ck 13 (by simp)).trans ((bk1 13 (by simp)).trans a13))
    ((ck 9 (by simp)).trans ((bk1 9 (by simp)).trans ((ak 9 (by simp)).trans F.e9)))
    ((ck 4 (by simp)).trans ((bk1 4 (by simp)).trans ((ak 4 (by simp)).trans F.e4)))
    hsf8 hdntop3 hD
  refine Fv256.B.reachesRet_trans64 h4 ?_
  intro S4 _ ⟨R4, fl4, M4, hS4, d4, d5, d14, dkn, dlt, dc8, dc0, d90, fr4⟩
  subst hS4
  -- the arithmetic of the division
  have hDpos : 0 < Fv256.B.wv M dp n := by
    have h1 := Fv256.B.wv_ge_top M dp n hn
    have h3 : 1 ≤ M.readLE (dp + 8 * (n - 1)) 8 := Nat.pos_of_ne_zero F.dtop
    have h5 : 2 ^ (64 * (n - 1)) ≤ M.readLE (dp + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) := Nat.le_mul_of_pos_left _ h3
    have h6 : 0 < 2 ^ (64 * (n - 1)) := Nat.two_pow_pos _
    omega
  rw [hUn, hDn] at dkn
  rw [hDn] at dlt
  have hdiv := Fv256.B.norm_div_eq (Fv256.B.wv M up ulen) (Fv256.B.wv M dp n) (2 ^ s) (Fv256.B.wv M4 qp (ulen + 1 - n))
    (Fv256.B.wv M4 (sp0 - 0xf0 + 0x48) n) (Nat.two_pow_pos _) hDpos dkn dlt
  have hUD : Fv256.B.wv M0 up L = Fv256.B.wv M up ulen := by
    rw [← F.uwv]; exact (Fv256.B.wv_of_frame M0 M _ hfr up L (by simp [Outside]; omega)).symm
  have hDD : Fv256.B.wv M0 dp 4 = Fv256.B.wv M dp n := by
    rw [← F.dwv]; exact (Fv256.B.wv_of_frame M0 M _ hfr dp 4 (by simp [Outside]; omega)).symm
  -- the quotient
  have hqw : ∀ j, j < L → M0.readLE (qp + 8 * j) 8 = 0 := Fv256.B.wv_zero_word M0 qp L hq0
  have hq4 : Fv256.B.wv M4 qp L = Fv256.B.wv M4 qp (ulen + 1 - n) := by
    refine Fv256.B.wv_ext M4 qp (ulen + 1 - n) 4 (by omega) (fun j hj1 hj2 => ?_)
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), hfr.readLE _ _ (by simp [Outside] <;> omega)]
    exact hqw j hj2
  have hQ : Fv256.B.wv M4 qp L = Fv256.B.wv M0 up L / Fv256.B.wv M0 dp 4 := by
    rw [hq4, hdiv.1, hUD, hDD]
  have hsfx : sp0 - 0xf0 + 0x138 ≤ 2 ^ 48 := by omega
  have fr134 : MemFrame M0 M4 [(qp, qp + 8 * L), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] := by
    have a1 : MemFrame M0 M3 [(qp, qp + 8 * L), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] :=
      hfr.trans fr13 (by intro a n' h; simp [Outside] at h ⊢; omega)
    exact a1.trans fr4 (by intro a n' h; simp [Outside] at h ⊢; omega)
  have hMs5 : M4.accessible (sp0 - 0xf0) 0x138 true = true := by
    rw [fr4.accessible, fr13.accessible, hfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have hMs6 : M4.accessible (sp0 - 0xf0) 0xf8 true = true := Janus.Arm64.Memory.accessible_mono _ hMs5 (by omega) (by omega)
  have hsb8' : M4.readLE (sp0 - 0xf0 + 0xb8) 8 = n := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr3.readLE _ _ (by simp [Outside] <;> omega)]; exact hsb8
  have se8 : M4.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), show sp0 - 0xf0 + 0xe8 = sp0 - 8 by omega]
    exact F.s_e8
  have sf0 : M4.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by
    rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega), show sp0 - 0xf0 + 0xf0 = sp0 by omega]
    exact F.s_f0
  by_cases hr0 : remp = 0
  · subst hr0
    have s130 : M4.readLE (sp0 - 0xf0 + 0x130) 8 = 0 := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.s_130
    have h5 := Fv256.Amd64.UdivremG.den_nil s0 (sp0 - 0xf0) R4 fl4 M4 hsfx hMs5 (by omega) d4 s130
    refine Fv256.B.reachesRet_trans64 h5 ?_
    intro S5 _ ⟨R5, fl5, hS5, k5⟩
    subst hS5
    have h6 := Fv256.Amd64.UdivremF.epilogue s0 (sp0 - 0xf0) rbpv ra R5 fl5 M4 (by omega) (by omega) hMs6 ((k5 4 (by simp)).trans d4) se8 sf0 hra47
    refine Fv256.B.reachesRet_mono64 h6 ?_
    rintro S ⟨R6, fl6, hS6, h64, h65, h614⟩
    refine ⟨R6, fl6, s0.xmm, M4, by rw [hS6], ?_, h65, ?_, rfl, hQ, ?_, ⟨fun _ => fr134, fun h => absurd rfl h⟩⟩
    · rw [h64, sp_arith sp0 hsp0]
    · rw [h614, k5 14 (by simp), d14]; exact hR3_14.trans hg
    · intro h; exact absurd rfl h
  · obtain ⟨hr48, hra, hr0z⟩ := hrem hr0
    have hrs' := hrs hr0
    have hqr' := hqr hr0
    have hru' := hru hr0
    have frx : MemFrame M0 M4 [(qp, qp + 8 * L), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] := by
      have a1 : MemFrame M0 M3 [(qp, qp + 8 * L), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] :=
        hfr.trans fr13 (by intro a n' h; simp [Outside] at h ⊢; omega)
      exact a1.trans fr4 (by intro a n' h; simp [Outside] at h ⊢; omega)
    have hra4 : M4.accessible remp 32 true = true := by rw [fr134.accessible]; exact hra
    have m130 : M4.readLE (sp0 - 0xf0 + 0x130) 8 = remp := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.s_130
    have md0 : M4.readLE (sp0 - 0xf0 + 0xd0) 8 = 18446744073709551615 := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega)]; exact cd0
    have md8 : M4.readLE (sp0 - 0xf0 + 0xd8) 8 = 18446744073709551616 - (64 - s) := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega)]; exact cd8
    have me0 : M4.readLE (sp0 - 0xf0 + 0xe0) 8 = n - 1 := by
      rw [fr4.readLE _ _ (by simp [Outside] <;> omega), fr13.readLE _ _ (by simp [Outside] <;> omega)]; exact F.s_e0
    have h5 := Fv256.Amd64.UdivremF.den_setup hL s0 remp n ulen s (sp0 - 0xf0) R4 fl4 M4 hs63 hn4 hn hul4 hr0 hremB hsfx hMs5 (by omega) d4
      m130 md0 me0 d90 dc0 dc8 md8
    refine Fv256.B.reachesRet_trans64 h5 ?_
    intro S5 _ ⟨R5, fl5, hS5, f9, f2, f3, f0, f6, f7, f8, f1, f4, f14⟩
    subst hS5
    have hdsj : remp + 32 ≤ sp0 - 0xf0 ∨ sp0 - 0xf0 + 0x138 ≤ remp := by omega
    have h6 := Fv256.Amd64.UdivremF.den_loop hL s0 remp n ulen s (sp0 - 0xf0) hs63 hn4 hn hge hul4 hr48 hsfx (by omega) hdsj (n - 1) 0 (by omega)
      R5 fl5 M4 hra4 hMs5 f9 f2 f3 f0 f6 f7 f8 f1 f4
    refine Fv256.B.reachesRet_trans64 h6 ?_
    intro S6 _ ⟨R6, fl6, M6, hS6, l9, lk, lmem, lfr⟩
    subst hS6
    have lfr' : MemFrame M4 M6 [(remp, remp + 8 * (n - 1))] := lfr.mono (by intro a n' h; simp [Outside] at h ⊢; omega)
    have hra6 : M6.accessible remp 32 true = true := by rw [lfr'.accessible]; exact hra4
    have hMs6' : M6.accessible (sp0 - 0xf0) 0x138 true = true := by rw [lfr'.accessible]; exact hMs5
    have mb8 : M6.readLE (sp0 - 0xf0 + 0xb8) 8 = n := by
      rw [lfr'.readLE _ _ (by simp [Outside] <;> omega)]; exact hsb8'
    have h7 := Fv256.Amd64.UdivremF.den_final hL s0 remp n ulen s (sp0 - 0xf0) R6 fl6 M6 hs63 hn4 hn hge hul4 hr48 hra6 hsfx hMs6' (by omega) hdsj
      ((lk 2 (by simp)).trans f2) ((lk 0 (by simp)).trans f0) ((lk 1 (by simp)).trans f1) ((lk 4 (by simp)).trans f4) mb8
    refine Fv256.B.reachesRet_trans64 h7 ?_
    intro S7 _ ⟨R7, fl7, M7, hS7, g4, gk, gval, gfr⟩
    subst hS7
    have frA : MemFrame M4 M7 [(remp, remp + 8 * n)] :=
      lfr'.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)
    have hM6 : ∀ a, (a + 8 ≤ remp ∨ remp + 32 ≤ a) → M6.readLE a 8 = M4.readLE a 8 := fun a h =>
      lfr'.readLE _ _ (by simp [Outside]; omega)
    have hMs7 : M7.accessible (sp0 - 0xf0) 0xf8 true = true := by rw [frA.accessible]; exact hMs6
    have se8' : M7.readLE (sp0 - 0xf0 + 0xe8) 8 = rbpv := by
      rw [frA.readLE _ _ (by simp [Outside] <;> omega)]; exact se8
    have sf0' : M7.readLE (sp0 - 0xf0 + 0xf0) 8 = ra := by
      rw [frA.readLE _ _ (by simp [Outside] <;> omega)]; exact sf0
    -- the remainder value
    have hRn : Fv256.B.wv M4 (sp0 - 0xf0 + 0x48) n = (Fv256.B.wv M up ulen % Fv256.B.wv M dp n) * 2 ^ s := hdiv.2
    have hw : Fv256.B.wv M7 remp n = Fv256.B.wv M4 (sp0 - 0xf0 + 0x48) n / 2 ^ s := by
      refine Fv256.B.shr_vec M4 M7 s (by omega) n (sp0 - 0xf0 + 0x48) remp (fun i hi => ?_)
      by_cases hin : i + 1 < n
      · rw [if_pos hin]
        have e1 : M7.readLE (remp + 8 * i) 8 = M6.readLE (remp + 8 * i) 8 :=
          gfr.readLE _ _ (by simp [Outside]; omega)
        rw [e1, lmem i (by omega) (by omega)]
      · rw [if_neg hin, Nat.add_zero]
        have hi' : i = n - 1 := by omega
        subst hi'
        rw [gval, hM6 _ (by omega)]
    have hrv : Fv256.B.wv M7 remp 4 = Fv256.B.wv M0 up L % Fv256.B.wv M0 dp 4 := by
      have hz := Fv256.B.wv_zero_word M0 remp 4 hr0z
      rw [Fv256.B.wv_ext M7 remp n 4 hn4 (fun j h1 h2 => ?_), hw, hRn, Nat.mul_div_cancel _ (Nat.two_pow_pos s), hUD, hDD]
      rw [frA.readLE _ _ (by simp [Outside]; omega), frx.readLE _ _ (by simp [Outside]; omega)]
      exact hz j h2
    have fr7 : MemFrame M0 M7 [(qp, qp + 8 * L), (remp, remp + 32), (sp0 - 0x148, sp0), (sp0 + 8, sp0 + 0x48)] :=
      frx.trans frA (by intro a n' h; simp [Outside] at h ⊢; omega)
    have hq7 : Fv256.B.wv M7 qp L = Fv256.B.wv M4 qp L :=
      Fv256.B.wv_of_frame M4 M7 _ frA qp L (by simp [Outside]; omega)
    have h8 := Fv256.Amd64.UdivremF.epilogue s0 (sp0 - 0xf0) rbpv ra R7 fl7 M7 (by omega) (by omega) hMs7 g4 se8' sf0' hra47
    refine Fv256.B.reachesRet_mono64 h8 ?_
    rintro S ⟨R8, fl8, hS8, h84, h85, h814⟩
    refine ⟨R8, fl8, s0.xmm, M7, by rw [hS8], ?_, h85, ?_, rfl, ?_, fun _ => hrv, ⟨fun h => absurd h hr0, fun _ => fr7⟩⟩
    · rw [h84, sp_arith sp0 hsp0]
    · rw [h814, gk 14 (by simp), lk 14 (by simp), f14, d14]; exact hR3_14.trans hg
    · rw [hq7]; exact hQ

end Fv256.Amd64.UdivremI
