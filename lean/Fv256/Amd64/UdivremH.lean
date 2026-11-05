import Fv256.ChainProg
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
import Fv256.Amd64.UdivremG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremH

/-- State of `udivrem` at the end of the front part (just after the `uLen` loop, `+0x1a0`). -/
structure Front (L : Nat) (R : Nat → W64) (M M0 : Memory) (sp0 dp qp qcap ql up remp n ulen s rbpv ra : Nat) : Prop where
  hn : 1 ≤ n
  hn4 : n ≤ 4
  hulen : ulen ≤ L
  hs : s ≤ 63
  e12 : R 12 = BitVec.ofNat 64 ulen
  e2 : R 2 = BitVec.ofNat 64 n
  e6 : R 6 = BitVec.ofNat 64 L
  e7 : R 7 = BitVec.ofNat 64 up
  e10 : R 10 = BitVec.ofNat 64 remp
  e4 : R 4 = BitVec.ofNat 64 (sp0 - 0xf0)
  e0 : R 0 = BitVec.ofNat 64 qp
  e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s)
  e3 : R 3 = BitVec.ofNat 64 ql
  e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s)
  e8 : R 8 = 0 - BitVec.ofNat 64 s
  e13 : R 13 = BitVec.ofNat 64 (63 - s)
  e15 : R 15 = 18446744073709551615#64
  e9 : R 9 = BitVec.ofNat 64 qcap
  -- the divisor and its normalised copy
  dwv : Fv256.B.wv M dp 4 = Fv256.B.wv M dp n
  dtop : M.readLE (dp + 8 * (n - 1)) 8 ≠ 0
  clz : s = Janus.Arm64.clzNat 64 (M.readLE (dp + 8 * (n - 1)) 8)
  dn : Fv256.B.wv M (sp0 - 0xf0 + 0x98) n = Fv256.B.wv M dp n * 2 ^ s
  dntop : 2 ^ 63 ≤ M.readLE (sp0 - 0xf0 + 0x98 + 8 * (n - 1)) 8
  -- the numerator
  uwv : Fv256.B.wv M up L = Fv256.B.wv M up ulen
  utop : 0 < ulen → M.readLE (up + 8 * (ulen - 1)) 8 ≠ 0
  -- the memory outside the arrays
  frame : MemFrame M0 M [(sp0 - 0xf0 + 0x98, sp0 - 0xf0 + 0xb8), (sp0 - 0xf0 + 0xd8, sp0 - 0xf0 + 0xe8),
    (sp0 - 0xf0 + 0xf8, sp0 - 0xf0 + 0x118), (sp0 - 0xf0 + 0x130, sp0 - 0xf0 + 0x138), (sp0 - 8, sp0)]
  s_d8 : M.readLE (sp0 - 0xf0 + 0xd8) 8 = 64 - s
  s_e0 : M.readLE (sp0 - 0xf0 + 0xe0) 8 = n - 1
  s_f8 : M.readLE (sp0 - 0xf0 + 0xf8) 8 = qp
  s_100 : M.readLE (sp0 - 0xf0 + 0x100) 8 = ql
  s_108 : M.readLE (sp0 - 0xf0 + 0x108) 8 = qcap
  s_110 : M.readLE (sp0 - 0xf0 + 0x110) 8 = up
  s_130 : M.readLE (sp0 - 0xf0 + 0x130) 8 = remp
  s_e8 : M.readLE (sp0 - 8) 8 = rbpv
  s_f0 : M.readLE sp0 8 = ra

set_option maxHeartbeats 16000000 in
theorem front {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (R : Nat → W64) (fl : Flags) (M0 : Memory) (sp0 dp qp qcap ql up remp : Nat)
    (hx15 : s0.xmm 15 = 0)
    (e4 : R 4 = BitVec.ofNat 64 sp0) (e9 : R 9 = BitVec.ofNat 64 dp) (e0 : R 0 = BitVec.ofNat 64 qp) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e1 : R 1 = BitVec.ofNat 64 qcap) (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e6 : R 6 = BitVec.ofNat 64 L)
    (hqp : qp < 2 ^ 64) (hql : ql < 2 ^ 64) (hqc : qcap < 2 ^ 64) (hup : up < 2 ^ 64) (hremp : remp < 2 ^ 64)
    (hsp0 : 0x150 ≤ sp0) (hsp : sp0 + 0x48 ≤ 2 ^ 48) (hMs : M0.accessible (sp0 - 0x148) 0x190 true = true)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M0.accessible dp 32 false = true) (hdisj : dp + 32 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ dp)
    (hup48 : up + 8 * L ≤ 2 ^ 48) (hua : M0.accessible up (8 * L) false = true) (hdisju : up + 8 * L ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ up)
    (hg1 : (R 14).toNat + 24 ≤ 2 ^ 48) (hg2 : M0.accessible ((R 14).toNat + 16) 8 false = true)
    (hg3 : M0.readLE ((R 14).toNat + 16) 8 < sp0 - 0xf8) (hgd : (R 14).toNat + 24 ≤ sp0 - 0x148 ∨ sp0 + 0x48 ≤ (R 14).toNat + 16)
    (hD0 : Fv256.B.wv M0 dp 4 ≠ 0) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x1a0))
      { s0 with regs := R, rip := BitVec.ofNat 64 ku, flags := fl, mem := M0 }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (kr : Nat → W64) (n ulen s : Nat),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl', mem := M', kreg := kr } ∧
        Front L R' M' M0 sp0 dp qp qcap ql up remp n ulen s (R 5).toNat (M0.readLE sp0 8) ∧ R' 5 = BitVec.ofNat 64 (sp0 - 8) ∧ R' 14 = R 14) := by
  have h1 := Fv256.Amd64.UdivremG.pro1 s0 sp0 dp R fl M0 hsp0 (by omega) (Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)) hdp hda (by omega) hg1 hg2 (by omega) (by omega) e4 e9
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 _ ⟨R1, fl1, M1, hS1, r2, r4, r5, rk, m5, m0, m7, fr1⟩
  subst hS1
  have hdw : ∀ k, k ≤ 3 → M1.readLE (dp + 8 * k) 8 = M0.readLE (dp + 8 * k) 8 := fun k hk =>
    fr1.readLE _ _ (by simp [Outside] <;> omega)
  have hda1 : M1.accessible dp 32 false = true := by rw [fr1.accessible]; exact hda
  have hwd1 : Fv256.B.wv M1 dp 4 = Fv256.B.wv M0 dp 4 := Fv256.B.wv_of_frame M0 M1 _ fr1 dp 4 (by simp [Outside] <;> omega)
  have h2 := Fv256.Amd64.UdivremA.dlen_loop s0 dp M1 hdp hda1 4 R1 fl1 (Nat.le_refl _) ((rk 9 (by simp)).trans e9) r2
    (fun j h1 h2 => by omega)
  refine Fv256.B.reachesRet_trans64 h2 ?_
  intro S2 _ ⟨R2, fl2, n, hS2, q2, hn4, hz, hnz, hk2⟩
  subst hS2
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso; apply hD0
      rw [← hwd1, Fv256.B.wv_ext M1 dp n 4 (by omega) (fun j hj1 hj2 => hz j hj1 hj2)]
      subst h; rfl
    · exact h
  have hnz1 := hnz hn1
  have hsf : sp0 - 0xf0 + 0x138 ≤ 2 ^ 48 := by omega
  have hMs1 : M1.accessible (sp0 - 0xf0) 0x138 true = true := by
    rw [fr1.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMs (by omega) (by omega)
  have hdtB : M1.readLE (dp + n * 8 - 8) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M1 (dp + n * 8 - 8) 8; simpa using this
  have hdt : M1.readLE (dp + n * 8 - 8) 8 = M1.readLE (dp + 8 * (n - 1)) 8 := by congr 1; omega
  have hR2_4 : R2 4 = BitVec.ofNat 64 (sp0 - 0xf0) := (hk2 4 (by simp)).trans r4
  have h3 := Fv256.Amd64.UdivremG.pro2 s0 dp n (sp0 - 0xf0) qp ql qcap up remp R2 fl2 M1 hn4 hn1 _ rfl
    (by rw [hdt]; exact hnz1) hdtB hdp hda1 hsf hMs1 (by omega) (by omega) q2 ((hk2 9 (by simp)).trans ((rk 9 (by simp)).trans e9)) hR2_4
    ((hk2 0 (by simp)).trans ((rk 0 (by simp)).trans e0)) ((hk2 3 (by simp)).trans ((rk 3 (by simp)).trans e3))
    ((hk2 1 (by simp)).trans ((rk 1 (by simp)).trans e1)) ((hk2 7 (by simp)).trans ((rk 7 (by simp)).trans e7))
    ((hk2 10 (by simp)).trans ((rk 10 (by simp)).trans e10)) hx15 hqp hql hqc hup hremp
  refine Fv256.B.reachesRet_trans64 h3 ?_
  intro S3 _ ⟨R3, fl3, M3, kr3, hS3, f12, f11, f8, f13, f15, fk3, sd8, se0, sf8, s100, s108, s110, s130, zer, fr3⟩
  subst hS3
  obtain ⟨hs63, hn2', hn3'⟩ := Fv256.B.clz_norm (M1.readLE (dp + n * 8 - 8) 8) (by rw [hdt]; exact hnz1) hdtB
  generalize hsd : Janus.Arm64.clzNat 64 (M1.readLE (dp + n * 8 - 8) 8) = s at *
  have hdw3 : ∀ k, k ≤ 3 → M3.readLE (dp + 8 * k) 8 = M1.readLE (dp + 8 * k) 8 := fun k hk =>
    fr3.readLE _ _ (by simp [Outside] <;> omega)
  have hda3 : M3.accessible dp 32 false = true := by rw [fr3.accessible]; exact hda1
  have hMs3 : M3.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr3.accessible]; exact hMs1
  have hR3_4 : R3 4 = BitVec.ofNat 64 (sp0 - 0xf0) := (fk3 4 (by simp)).trans hR2_4
  have h4 := Fv256.Amd64.UdivremB.dn_loop { s0 with kreg := kr3 } dp qp qcap ql up remp n 4 s (sp0 - 0xf0) hs63 hn4 hn1 hdp hsf (by omega) (by omega)
    (n - 1) (by omega) R3 fl3 M3 hda3 hMs3 f12 ((fk3 0 (by simp)).trans ((hk2 0 (by simp)).trans ((rk 0 (by simp)).trans e0)))
    ((fk3 1 (by simp)).trans ((hk2 1 (by simp)).trans ((rk 1 (by simp)).trans e1)))
    ((fk3 3 (by simp)).trans ((hk2 3 (by simp)).trans ((rk 3 (by simp)).trans e3)))
    ((fk3 7 (by simp)).trans ((hk2 7 (by simp)).trans ((rk 7 (by simp)).trans e7)))
    ((fk3 10 (by simp)).trans ((hk2 10 (by simp)).trans ((rk 10 (by simp)).trans e10)))
    f11 f8 f13 f15 ((fk3 9 (by simp)).trans ((hk2 9 (by simp)).trans ((rk 9 (by simp)).trans e9))) hR3_4
    sd8 sf8 s108 s100 s110 s130 (fun k hk1 hk2 => by omega)
  refine Fv256.B.reachesRet_trans64 h4 ?_
  intro S4 _ ⟨R4, fl4, M4, hS4, g12, gk, gmem, gfr⟩
  subst hS4
  have hda4 : M4.accessible dp 32 false = true := by rw [gfr.accessible]; exact hda3
  have hMs4 : M4.accessible (sp0 - 0xf0) 0x138 true = true := by rw [gfr.accessible]; exact hMs3
  have h5 := Fv256.Amd64.UdivremC.mid1 hL { s0 with kreg := kr3 } dp qp qcap ql up remp n L s (sp0 - 0xf0) R4 fl4 M4 hs63 hn4 hn1 (by omega) (by omega) hdp hda4 hsf hMs4
    (by omega) (by omega) g12 ((gk 0 (by simp)).trans ((fk3 0 (by simp)).trans ((hk2 0 (by simp)).trans ((rk 0 (by simp)).trans e0))))
    ((gk 1 (by simp)).trans ((fk3 1 (by simp)).trans ((hk2 1 (by simp)).trans ((rk 1 (by simp)).trans e1))))
    ((gk 3 (by simp)).trans ((fk3 3 (by simp)).trans ((hk2 3 (by simp)).trans ((rk 3 (by simp)).trans e3))))
    ((gk 7 (by simp)).trans ((fk3 7 (by simp)).trans ((hk2 7 (by simp)).trans ((rk 7 (by simp)).trans e7))))
    ((gk 10 (by simp)).trans ((fk3 10 (by simp)).trans ((hk2 10 (by simp)).trans ((rk 10 (by simp)).trans e10))))
    ((gk 11 (by simp)).trans f11) ((gk 8 (by simp)).trans f8) ((gk 13 (by simp)).trans f13) ((gk 15 (by simp)).trans f15)
    ((gk 9 (by simp)).trans ((fk3 9 (by simp)).trans ((hk2 9 (by simp)).trans ((rk 9 (by simp)).trans e9))))
    ((gk 4 (by simp)).trans hR3_4)
    ((gk 2 (by simp)).trans ((fk3 2 (by simp)).trans q2))
    ((gk 6 (by simp)).trans ((fk3 6 (by simp)).trans ((hk2 6 (by simp)).trans ((rk 6 (by simp)).trans e6))))
    (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sd8) (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sf8)
    (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s108) (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s100)
    (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s110) (by rw [gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s130)
  refine Fv256.B.reachesRet_trans64 h5 ?_
  intro S5 _ ⟨R5, fl5, M5, hS5, a1, a9, a11, a12, a15, ak, hm0, fr5⟩
  subst hS5
  have hd5 : ∀ k, k ≤ 3 → M5.readLE (dp + 8 * k) 8 = M1.readLE (dp + 8 * k) 8 := fun k hk =>
    (fr5.readLE _ _ (by simp [Outside] <;> omega)).trans ((gfr.readLE _ _ (by simp [Outside] <;> omega)).trans (hdw3 k hk))
  have hua5 : M5.accessible up (8 * L) false = true := by rw [fr5.accessible, gfr.accessible, fr3.accessible, fr1.accessible]; exact hua
  have hMs5 : M5.accessible (sp0 - 0xf0) 0x138 true = true := by rw [fr5.accessible]; exact hMs4
  have hsf8 : M5.readLE (sp0 - 0xf0 + 0xf8) 8 = qp := by
    rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sf8
  have h6 := Fv256.Amd64.UdivremC.ulen_loop hL { s0 with kreg := kr3 } up qp M5 (sp0 - 0xf0) hup48 hua5 hsf (by omega) hMs5 (by omega) hsf8 hqp L R5 fl5
    (Nat.le_refl _)
    ((ak 7 (by simp)).trans ((gk 7 (by simp)).trans ((fk3 7 (by simp)).trans ((hk2 7 (by simp)).trans ((rk 7 (by simp)).trans e7)))))
    ((ak 4 (by simp)).trans ((gk 4 (by simp)).trans hR3_4))
    (by rw [a12]; bv_omega)
    ((ak 0 (by simp)).trans ((gk 0 (by simp)).trans ((fk3 0 (by simp)).trans ((hk2 0 (by simp)).trans ((rk 0 (by simp)).trans e0)))))
    (fun j h1 h2 => by omega)
  refine Fv256.B.reachesRet_trans64 h6 ?_
  intro S6 _ ⟨R6, fl6, ulen, hS6, b12, hle, hzz, hnz2, b0, bk⟩
  subst hS6
  have hall : ∀ k, k ∉ [0, 1, 2, 4, 5, 8, 9, 11, 12, 13, 15] → R6 k = R k := fun k hk => by
    have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 4 ∧ k ≠ 5 ∧ k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 ∧ k ≠ 15 := by simpa using hk
    exact (bk k (by simp; omega)).trans ((ak k (by simp; omega)).trans ((gk k (by omega)).trans
      ((fk3 k (by simp; omega)).trans ((hk2 k (by simp; omega)).trans (rk k (by simp; omega))))))
  -- the divisor words and the normalised divisor
  have hd5' : ∀ k, k ≤ 3 → M5.readLE (dp + 8 * k) 8 = M0.readLE (dp + 8 * k) 8 := fun k hk => (hd5 k hk).trans (hdw k hk)
  have hdz : ∀ j, n ≤ j → j < 4 → M5.readLE (dp + 8 * j) 8 = 0 := fun j h1 h2 => by rw [hd5 j (by omega)]; exact hz j h1 h2
  have hdwv : Fv256.B.wv M5 dp 4 = Fv256.B.wv M5 dp n := Fv256.B.wv_ext M5 dp n 4 (by omega) hdz
  have hdtop5 : M5.readLE (dp + 8 * (n - 1)) 8 = M1.readLE (dp + 8 * (n - 1)) 8 := hd5 (n - 1) (by omega)
  have hdn5 : ∀ k, k < n → M5.readLE (sp0 - 0xf0 + 0x98 + 8 * k) 8 =
      (M5.readLE (dp + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + Fv256.B.shc M5 dp s k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      simp only [Nat.mul_zero, Nat.add_zero, Fv256.B.shc, if_true]
      rw [hm0, fr5.readLE dp 8 (by simp [Outside] <;> omega)]
    · unfold Fv256.B.shc
      rw [if_neg (by omega)]
      rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gmem k h0 hk]
      rw [hd5 k (by omega), hd5 (k - 1) (by omega), hdw3 k (by omega), hdw3 (k - 1) (by omega)]
  obtain ⟨hdnw, hdntop⟩ := Fv256.B.dn_norm M5 M5 dp (sp0 - 0xf0 + 0x98) n s (M1.readLE (dp + n * 8 - 8) 8) hn1 hs63
    (by rw [hdtop5, ← hdt]) hn2' hn3' hdn5
  have hs5 : ∀ k, k ≤ 3 → M5.readLE (dp + 8 * k) 8 = M1.readLE (dp + 8 * k) 8 := hd5
  refine ⟨0, _, Janus.Amd64.Program.Steps.refl _, rfl, R6, fl6, M5, kr3, n, ulen, s, rfl, ⟨hn1, hn4, by omega, hs63, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hdwv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact b12
  · exact ((bk 2 (by simp)).trans ((ak 2 (by simp)).trans ((gk 2 (by simp)).trans ((fk3 2 (by simp)).trans q2))))
  · exact (hall 6 (by simp)).trans e6
  · exact (hall 7 (by simp)).trans e7
  · exact (hall 10 (by simp)).trans e10
  · exact ((bk 4 (by simp)).trans ((ak 4 (by simp)).trans ((gk 4 (by simp)).trans hR3_4)))
  · exact b0
  · exact (bk 1 (by simp)).trans a1
  · exact (hall 3 (by simp)).trans e3
  · exact (bk 11 (by simp)).trans a11
  · exact (bk 8 (by simp)).trans ((ak 8 (by simp)).trans ((gk 8 (by simp)).trans f8))
  · exact (bk 13 (by simp)).trans ((ak 13 (by simp)).trans ((gk 13 (by simp)).trans f13))
  · exact (bk 15 (by simp)).trans a15
  · exact (bk 9 (by simp)).trans a9
  · rw [hdtop5]; exact hnz1
  · rw [hdtop5, ← hdt]; exact hsd.symm
  · exact hdnw
  · exact hdntop
  · exact Fv256.B.wv_ext M5 up ulen L hle (fun j h1 h2 => hzz j h1 h2)
  · exact hnz2
  · have f13' : MemFrame M0 M3 [(sp0 - 0xf0 + 0x98, sp0 - 0xf0 + 0xb8), (sp0 - 0xf0 + 0xd8, sp0 - 0xf0 + 0xe8), (sp0 - 0xf0 + 0xf8, sp0 - 0xf0 + 0x118), (sp0 - 0xf0 + 0x130, sp0 - 0xf0 + 0x138), (sp0 - 8, sp0)] := fr1.trans fr3 (by intro a n' h; simp [Outside] at h ⊢; omega)
    have f14' : MemFrame M0 M4 [(sp0 - 0xf0 + 0x98, sp0 - 0xf0 + 0xb8), (sp0 - 0xf0 + 0xd8, sp0 - 0xf0 + 0xe8), (sp0 - 0xf0 + 0xf8, sp0 - 0xf0 + 0x118), (sp0 - 0xf0 + 0x130, sp0 - 0xf0 + 0x138), (sp0 - 8, sp0)] := f13'.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)
    exact f14'.trans fr5 (by intro a n' h; simp [Outside] at h ⊢; omega)
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sd8
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact se0
  · exact hsf8
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s100
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s108
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s110
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s130
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega), fr3.readLE _ _ (by simp [Outside] <;> omega)]
    exact m5
  · rw [fr5.readLE _ _ (by simp [Outside] <;> omega), gfr.readLE _ _ (by simp [Outside] <;> omega), fr3.readLE _ _ (by simp [Outside] <;> omega),
      fr1.readLE _ _ (by simp [Outside] <;> omega)]
  · exact (bk 5 (by simp)).trans ((ak 5 (by simp)).trans ((gk 5 (by simp)).trans ((fk3 5 (by simp)).trans ((hk2 5 (by simp)).trans r5))))
  · exact hall 14 (by simp)

end Fv256.Amd64.UdivremH
