import Fv256.Arm64.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Arm64.KnuthLem
import Fv256.Arm64.KnuthEst
import Fv256.Arm64.KnuthSub
import Fv256.Arm64.KnuthAdd
import Fv256.Arm64.KnuthPost
import Fv256.Arm64.KnuthIter
import Fv256.Arm64.KnuthDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.KnuthEst Fv256.Arm64.KnuthDefs
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.KnuthLoop

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- One iteration of the `udivremKnuth` outer loop: from the head with `k = j + 1` digits produced to the head with `k = j`. -/
theorem iter (s0 : State) (up dp qp n m ql v dl dh cap : Nat) (M0 : Memory) (R : Nat → W64) (fl : Flags)
    (M : Memory) (j : Nat) (K : KC up dp qp n m ql v dl dh cap s0.sp.toNat M0) (hj : j + n + 1 ≤ m)
    (hR : HeadR R (j + 1) v n m up dp dl dh cap) (hI : KInv M0 M up dp qp n m (j + 1)) :
    ReachesRet Fv256.Arm64.ChainProg.program (BitVec.ofNat 64 (kn + 0xbc))
      { s0 with regs := R, pc := BitVec.ofNat 64 (kn + 0xbc), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', pc := BitVec.ofNat 64 (kn + 0xbc), flags := fl', mem := M' } ∧
        HeadR R' j v n m up dp dl dh cap ∧ KInv M0 M' up dp qp n m j ∧ (∀ k, k ∉ Scratch → k ≠ 3 → R' k = R k)) := by
  obtain ⟨r0, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hR
  have hfr := hI.fr
  have K0 := K
  obtain ⟨hn, hn2, hm2, hmq, hql2, hdh, hdl, hdh63, hv, hcap, hcapB, hsp, hup, hdp, hqp, hdu, hqu, hqd, hus, hqs, hua, hda, hqa, hs88, hs96, s88, s96⟩ := K
  obtain ⟨hsp2, hsp3⟩ := hsp
  have hqlj : j < ql := by omega
  have r3' : R 3 = BitVec.ofNat 64 j := by rw [r3]; bv_omega
  have hu2B := Janus.Arm64.Memory.readLE_lt M (up + 8 * (j + n)) 8
  have hu1B := Janus.Arm64.Memory.readLE_lt M (up + 8 * (j + n - 1)) 8
  have hu0B := Janus.Arm64.Memory.readLE_lt M (up + 8 * (j + n - 2)) 8
  simp only [Nat.reducePow] at hu2B hu1B hu0B
  have hdlB : dl < 2 ^ 64 := by
    rw [hdl]; have := Janus.Arm64.Memory.readLE_lt M0 (dp + 8 * (n - 2)) 8; simpa using this
  have hdhB : dh < 2 ^ 64 := by
    rw [hdh]; have := Janus.Arm64.Memory.readLE_lt M0 (dp + 8 * (n - 1)) 8; simpa using this
  have hMu : M.accessible up (8 * m) true = true := by rw [hfr.accessible]; exact hua
  have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
  have hMq : M.accessible qp (8 * ql) true = true := by rw [hfr.accessible]; exact hqa
  have sm88 : M.readLE (s0.sp.toNat + 88) 8 = qp := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s88
  have sm96 : M.readLE (s0.sp.toNat + 96) 8 = ql := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s96
  obtain ⟨u2, hu2⟩ : ∃ u2, M.readLE (up + 8 * (j + n)) 8 = u2 := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, M.readLE (up + 8 * (j + n - 1)) 8 = u1 := ⟨_, rfl⟩
  obtain ⟨u0, hu0⟩ : ∃ u0, M.readLE (up + 8 * (j + n - 2)) 8 = u0 := ⟨_, rfl⟩
  rw [hu2] at hu2B
  rw [hu1] at hu1B
  rw [hu0] at hu0B
  have h1 := Fv256.Arm64.KnuthIter.est_all { s0 with regs := R, pc := BitVec.ofNat 64 (kn + 0xbc), flags := fl, mem := M }
    up dp n m j v dl dh u2 u1 u0 cap hn hn2 hj hm2 hcap hcapB hdh63 hdhB hdlB hu2B hu1B hu0B hv hMu (by omega)
    r0 r2 r3' r4 r5 r6 r7 r8 r9 r10 hu2 hu1 hu0 rfl
  refine Fv256.B.reachesRet_trans h1 ?_
  intro S1 hrip ⟨R1, fl1, qh, hS1, hqh, hqhB, q14, q13, q11, q15, q12, q1, qu⟩
  subst hS1
  have h2 := Fv256.Arm64.KnuthSub.submul_loop { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M }
    (up + 8 * j) dp n qh M hn hn2 hqhB
    (Janus.Arm64.Memory.accessible_mono _ hMu (by omega) (by omega)) (by omega) hMd (by omega) (by omega)
    n 0 R1 fl1 M (by omega) ((qu 8 (by simp [Scratch])).trans r8) (by rw [q11]; rfl) q14 q12
    ((qu 6 (by simp [Scratch])).trans r6) (fun k _ => rfl) (by simp [Fv256.B.wv, q15]) (MemFrame.refl _ _)
  refine Fv256.B.reachesRet_trans h2 ?_
  intro S2 hrip2 ⟨R2, fl2, M2, hS2, p11, pu, pI, pfr⟩
  subst hS2
  have hscr : ∀ k, k ∉ Scratch → R1 k = R k := fun k hk => qu k (by simp [Scratch] at hk ⊢; omega)
  obtain ⟨b, hb⟩ : ∃ b, b = (R2 15).toNat := ⟨_, rfl⟩
  have hbB : b < 2 ^ 64 := by rw [hb]; exact (R2 15).isLt
  have e15 : R2 15 = BitVec.ofNat 64 b := by rw [hb]; simp
  have g1 : R2 1 = BitVec.ofNat 64 (j + n) := (pu 1 (by simp)).trans q1
  have g3 : R2 3 = BitVec.ofNat 64 j := (pu 3 (by simp)).trans ((hscr 3 (by simp [Scratch])).trans r3')
  have g6 : R2 6 = BitVec.ofNat 64 dp := (pu 6 (by simp)).trans ((hscr 6 (by simp [Scratch])).trans r6)
  have g8 : R2 8 = BitVec.ofNat 64 n := (pu 8 (by simp)).trans ((hscr 8 (by simp [Scratch])).trans r8)
  have g9 : R2 9 = BitVec.ofNat 64 up := (pu 9 (by simp)).trans ((hscr 9 (by simp [Scratch])).trans r9)
  have g12 : R2 12 = BitVec.ofNat 64 (up + 8 * j) := (pu 12 (by simp)).trans q12
  have g13 : R2 13 = BitVec.ofNat 64 u2 := (pu 13 (by simp)).trans q13
  have g14 : R2 14 = BitVec.ofNat 64 qh := (pu 14 (by simp)).trans q14
  have hM2a : M2.accessible up (8 * m) true = true := by rw [pfr.accessible]; exact hMu
  have hM2q : M2.accessible qp (8 * ql) true = true := by rw [pfr.accessible]; exact hMq
  have hM2s88 : M2.accessible (s0.sp.toNat + 88) 8 false = true := by rw [pfr.accessible]; rw [hfr.accessible]; exact hs88
  have hM2s96 : M2.accessible (s0.sp.toNat + 96) 8 false = true := by rw [pfr.accessible]; rw [hfr.accessible]; exact hs96
  have rm88 : M2.readLE (s0.sp.toNat + 88) 8 = qp := by rw [pfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm88
  have rm96 : M2.readLE (s0.sp.toNat + 96) 8 = ql := by rw [pfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm96
  have hDeq : Fv256.B.wv M dp n = Fv256.B.wv M0 dp n :=
    Fv256.B.wv_of_frame M0 M _ hfr dp n (by simp [Outside]; omega)
  have hsub : Fv256.B.wv M (up + 8 * j) n + b * 2 ^ (64 * n) = Fv256.B.wv M2 (up + 8 * j) n + qh * Fv256.B.wv M0 dp n := by
    rw [← hDeq, hb]; exact pI
  have hu2' : M.readLE (up + 8 * j + 8 * n) 8 = u2 := by rw [← hu2]; congr 1; omega
  have hXs : Fv256.B.wv M (up + 8 * j) (n + 1) = u2 * 2 ^ (64 * n) + Fv256.B.wv M (up + 8 * j) n := by
    rw [Fv256.B.wv_snoc, hu2']
    have := Nat.mul_comm (2 ^ (64 * n)) u2
    omega
  have hRlt := hI.i2
  have hXu : Fv256.B.wv M (up + 8 * j) (n + 1) =
      M.readLE (up + 8 * j) 8 + 2 ^ 64 * Fv256.B.wv M (up + 8 * (j + 1)) n := by
    rw [Fv256.B.wv_succ, show up + 8 * j + 8 = up + 8 * (j + 1) by omega]
  have huj : M.readLE (up + 8 * j) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * j) 8; simpa using this
  have hXD : Fv256.B.wv M (up + 8 * j) (n + 1) < 2 ^ 64 * Fv256.B.wv M0 dp n := by
    rw [hXu]
    have := Nat.mul_le_mul_left (2 ^ 64) (show Fv256.B.wv M (up + 8 * (j + 1)) n + 1 ≤ Fv256.B.wv M0 dp n by omega)
    rw [Nat.mul_add] at this
    omega
  have hok := Fv256.B.est_ok M M0 (up + 8 * j) dp n hn (Fv256.B.wv M0 dp n) _ dh dl u2 u1 u0 rfl rfl hdh hdl
    hu2'.symm (by rw [← hu1]; congr 1; omega) (by rw [← hu0]; congr 1; omega) hdh63 hXD
  rw [← hqh] at hok
  have hDlt : Fv256.B.wv M0 dp n < 2 ^ (64 * n) := Fv256.B.wv_lt M0 dp n
  have hcore := Fv256.B.iter_core (2 ^ (64 * n)) (Fv256.B.wv M0 dp n) (Fv256.B.wv M (up + 8 * j) (n + 1))
    (Fv256.B.wv M (up + 8 * j) n) u2 qh b (Fv256.B.wv M2 (up + 8 * j) n) hDlt (by omega) (Fv256.B.wv_lt M _ _) hXs hok hsub
    (Fv256.B.wv_lt M2 _ _)
  have hrB : Fv256.B.wv M2 (up + 8 * j) n < 2 ^ (64 * n) := Fv256.B.wv_lt M2 _ _
  have hsum := Nat.div_add_mod (Fv256.B.wv M (up + 8 * j) (n + 1)) (Fv256.B.wv M0 dp n)
  have hw2a : M2.accessible (up + 8 * (j + n)) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono _ hM2a (by omega) (by omega)
  have hsp3' : s0.sp.toNat + 120 ≤ 2 ^ 48 := hsp3
  by_cases hbu : b ≤ u2
  · rcases hcore with ⟨_, hqq, hrr⟩ | ⟨hlt, _⟩
    · have h3 := Fv256.Arm64.KnuthPost.post_sub_ok
        { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 }
        up j n b u2 M2 hbu hu2B hw2a (by omega) g1 g9 g13 e15 rfl rfl
      refine Fv256.B.reachesRet_trans h3 ?_
      intro S3 hrip3 ⟨R3, fl3, M3, hS3, w1, wfr, wu⟩
      subst hS3
      have hM3q : M3.accessible qp (8 * ql) true = true := by rw [wfr.accessible]; exact hM2q
      have hM3s88 : M3.accessible (s0.sp.toNat + 88) 8 false = true := by rw [wfr.accessible]; exact hM2s88
      have hM3s96 : M3.accessible (s0.sp.toNat + 96) 8 false = true := by rw [wfr.accessible]; exact hM2s96
      have wm88 : M3.readLE (s0.sp.toNat + 88) 8 = qp := by rw [wfr.readLE _ _ (by simp [Outside] <;> omega)]; exact rm88
      have wm96 : M3.readLE (s0.sp.toNat + 96) 8 = ql := by rw [wfr.readLE _ _ (by simp [Outside] <;> omega)]; exact rm96
      have h4 := Fv256.Arm64.KnuthPost.tail_store
        { { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 } with regs := R3, pc := BitVec.ofNat 64 (kn + 0x1cc), flags := fl3, mem := M3 }
        qp ql j qh M3 hqlj hqhB hql2 hM3q hqp hsp2 hsp3'
        ((wu 3 (by simp)).trans g3) ((wu 14 (by simp)).trans g14) wm96 wm88 hM3s96 hM3s88 rfl rfl
      refine Fv256.B.reachesRet_mono h4 ?_
      intro S4 ⟨R4, fl4, M4, hS4, t3, trd, tfr, tu⟩
      subst hS4
      have hpres : ∀ k, k ∉ Scratch → k ≠ 3 → R4 k = R k := by
        intro k hk hk3
        have a1 : k ∉ [1, 3, 11] := by simp [Scratch] at hk ⊢; omega
        have a2 : k ∉ [11] := by simp [Scratch] at hk ⊢; omega
        have a3 : k ∉ [11, 15, 16, 17, 19, 20, 21] := by simp [Scratch] at hk ⊢; omega
        exact (tu k a1).trans ((wu k a2).trans ((pu k a3).trans ((hscr k hk))))
      have hF24 : MemFrame M2 M4 [(up + 8 * (j + n), up + 8 * (j + n) + 8), (qp + 8 * j, qp + 8 * j + 8)] :=
        wfr.trans tfr (by intro a n' h; simp [Outside] at h ⊢; omega)
      have hFa : MemFrame M M3 (LRanges up qp j m) := pfr.trans wfr
        (by intro a n' h; simp [LRanges, Outside] at h; simp [Outside]; omega)
      have hFb : MemFrame M M4 (LRanges up qp j m) := hFa.trans tfr
        (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)
      have hw1 : Fv256.B.wv M4 (up + 8 * j) n = Fv256.B.wv M2 (up + 8 * j) n :=
        Fv256.B.wv_of_frame M2 M4 _ hF24 (up + 8 * j) n (by simp [Outside]; omega)
      refine ⟨R4, fl4, M4, rfl, ?_, ?_, hpres⟩
      · exact ⟨(hpres 0 (by simp [Scratch]) (by omega)).trans r0, (hpres 2 (by simp [Scratch]) (by omega)).trans r2, t3,
          (hpres 4 (by simp [Scratch]) (by omega)).trans r4, (hpres 5 (by simp [Scratch]) (by omega)).trans r5,
          (hpres 6 (by simp [Scratch]) (by omega)).trans r6, (hpres 7 (by simp [Scratch]) (by omega)).trans r7,
          (hpres 8 (by simp [Scratch]) (by omega)).trans r8, (hpres 9 (by simp [Scratch]) (by omega)).trans r9,
          (hpres 10 (by simp [Scratch]) (by omega)).trans r10⟩
      · rw [← hqq, ← hrr] at hsum
        exact kinv_finish up dp qp n m ql v dl dh cap M0 M M4 s0.sp.toNat j qh _ K0 hj hI hFb hw1 trd hsum
          (by rw [hrr]; exact Nat.mod_lt _ (by omega))
    · exact absurd hbu (Nat.not_le.mpr hlt)
  · rcases hcore with ⟨hle, _⟩ | ⟨hlt, hqq, hPle, hrr⟩
    · exact absurd hle hbu
    · have hqh1 : 1 ≤ qh := by rw [hqq]; exact Nat.le_add_left 1 _
      have hbB' : u2 < b := hlt
      have h3 := Fv256.Arm64.KnuthPost.post_sub_borrow
        { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 }
        up j n b u2 M2 hbB' hbB hw2a (by omega) g1 g9 g13 e15 rfl rfl
      refine Fv256.B.reachesRet_trans h3 ?_
      intro S3 hrip3 ⟨R3, fl3, M3, hS3, w11, w13, wval, wfr, wu⟩
      subst hS3
      have hM3a : M3.accessible up (8 * m) true = true := by rw [wfr.accessible]; exact hM2a
      have hM3q : M3.accessible qp (8 * ql) true = true := by rw [wfr.accessible]; exact hM2q
      have hM3d : M3.accessible dp (8 * n) false = true := by rw [wfr.accessible, pfr.accessible]; exact hMd
      have hM3s88 : M3.accessible (s0.sp.toNat + 88) 8 false = true := by rw [wfr.accessible]; exact hM2s88
      have hM3s96 : M3.accessible (s0.sp.toNat + 96) 8 false = true := by rw [wfr.accessible]; exact hM2s96
      have wm88 : M3.readLE (s0.sp.toNat + 88) 8 = qp := by rw [wfr.readLE _ _ (by simp [Outside] <;> omega)]; exact rm88
      have wm96 : M3.readLE (s0.sp.toNat + 96) 8 = ql := by rw [wfr.readLE _ _ (by simp [Outside] <;> omega)]; exact rm96
      have h4 := Fv256.Arm64.KnuthAdd.addback_loop
        { { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 } with regs := R3, pc := BitVec.ofNat 64 (kn + 0x210), flags := fl3, mem := M3 }
        (up + 8 * j) dp n M3 hn hn2 (Janus.Arm64.Memory.accessible_mono _ hM3a (by omega) (by omega)) (by omega) hM3d (by omega) (by omega)
        n 0 0 R3 fl3 M3 (by omega) (by omega) ((wu 8 (by simp)).trans g8) w11 w13 ((wu 12 (by simp)).trans g12)
        ((wu 6 (by simp)).trans g6) (fun k _ => rfl) (by simp [Fv256.B.wv]) (MemFrame.refl _ _)
      refine Fv256.B.reachesRet_trans h4 ?_
      intro S4 hrip4 ⟨R4, fl4, M4, c', hS4, hc', c13, cu, cI, cfr⟩
      subst hS4
      have hD3 : Fv256.B.wv M3 dp n = Fv256.B.wv M0 dp n := by
        rw [Fv256.B.wv_of_frame M2 M3 _ wfr dp n (by simp [Outside]; omega),
          Fv256.B.wv_of_frame M M2 _ pfr dp n (by simp [Outside]; omega), hDeq]
      have hw3 : Fv256.B.wv M3 (up + 8 * j) n = Fv256.B.wv M2 (up + 8 * j) n :=
        Fv256.B.wv_of_frame M2 M3 _ wfr (up + 8 * j) n (by simp [Outside]; omega)
      rw [hw3, hD3] at cI
      have hW4lt := Fv256.B.wv_lt M4 (up + 8 * j) n
      have hc1 : c' = 1 := by
        rcases (show c' = 0 ∨ c' = 1 by omega) with h | h
        · rw [h] at cI; omega
        · exact h
      subst hc1
      have hM4a : M4.accessible up (8 * m) true = true := by rw [cfr.accessible]; exact hM3a
      have hM4q : M4.accessible qp (8 * ql) true = true := by rw [cfr.accessible]; exact hM3q
      have hM4s88 : M4.accessible (s0.sp.toNat + 88) 8 false = true := by rw [cfr.accessible]; exact hM3s88
      have hM4s96 : M4.accessible (s0.sp.toNat + 96) 8 false = true := by rw [cfr.accessible]; exact hM3s96
      have cm88 : M4.readLE (s0.sp.toNat + 88) 8 = qp := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega)]; exact wm88
      have cm96 : M4.readLE (s0.sp.toNat + 96) 8 = ql := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega)]; exact wm96
      have hw4 : M4.readLE (up + 8 * (j + n)) 8 = 2 ^ 64 - b + u2 := by
        rw [cfr.readLE _ _ (by simp [Outside] <;> omega)]; exact wval
      have hM4w : M4.accessible (up + 8 * (j + n)) 8 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hM4a (by omega) (by omega)
      have h5 := Fv256.Arm64.KnuthPost.post_add
        { { { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 } with regs := R3, pc := BitVec.ofNat 64 (kn + 0x210), flags := fl3, mem := M3 } with regs := R4, pc := BitVec.ofNat 64 (kn + 0x218), flags := fl4, mem := M4 }
        up j n 1 (2 ^ 64 - b + u2) M4 (Nat.le_refl 1) (by omega) hM4w (by omega)
        ((cu 1 (by simp)).trans ((wu 1 (by simp)).trans g1)) ((cu 9 (by simp)).trans ((wu 9 (by simp)).trans g9)) c13 hw4 rfl rfl
      refine Fv256.B.reachesRet_trans h5 ?_
      intro S5 hrip5 ⟨R5, fl5, M5, hS5, d14, dval, dfr, du⟩
      subst hS5
      have h6 := Fv256.Arm64.KnuthPost.tail_store
        { { { { { s0 with regs := R1, pc := BitVec.ofNat 64 (kn + 0x1a8), flags := fl1, mem := M } with regs := R2, pc := BitVec.ofNat 64 (kn + 0x1b0), flags := fl2, mem := M2 } with regs := R3, pc := BitVec.ofNat 64 (kn + 0x210), flags := fl3, mem := M3 } with regs := R4, pc := BitVec.ofNat 64 (kn + 0x218), flags := fl4, mem := M4 } with regs := R5, pc := BitVec.ofNat 64 (kn + 0x1cc), flags := fl5, mem := M5 }
        qp ql j (qh - 1) M5 hqlj (by omega) hql2 (by rw [dfr.accessible]; exact hM4q) hqp hsp2 hsp3'
        ((du 3 (by simp)).trans ((cu 3 (by simp)).trans ((wu 3 (by simp)).trans g3)))
        (by
          have e : R5 14 = BitVec.ofNat 64 qh - 1#64 := by
            rw [d14]; show R4 14 - 1#64 = _; rw [(cu 14 (by simp)).trans ((wu 14 (by simp)).trans g14)]
          show R5 14 = _
          exact e.trans (bv_sub_one qh hqh1 hqhB))
        (by rw [dfr.readLE _ _ (by simp [Outside] <;> omega)]; exact cm96)
        (by rw [dfr.readLE _ _ (by simp [Outside] <;> omega)]; exact cm88)
        (by rw [dfr.accessible]; exact hM4s96) (by rw [dfr.accessible]; exact hM4s88) rfl rfl
      refine Fv256.B.reachesRet_mono h6 ?_
      intro S6 ⟨R6, fl6, M6, hS6, t3, trd, tfr, tu⟩
      subst hS6
      have hpres : ∀ k, k ∉ Scratch → k ≠ 3 → R6 k = R k := by
        intro k hk hk3
        have a1 : k ∉ [1, 3, 11] := by simp [Scratch] at hk ⊢; omega
        have a2 : k ∉ [11, 14, 15, 16, 17, 19, 20, 21] := by simp [Scratch] at hk ⊢; omega
        have a3 : k ∉ [11, 14] := by simp [Scratch] at hk ⊢; omega
        have a4 : k ∉ [11, 13, 15, 16, 17, 19, 20] := by simp [Scratch] at hk ⊢; omega
        have a5 : k ∉ [11, 13] := by simp [Scratch] at hk ⊢; omega
        have a6 : k ∉ [11, 15, 16, 17, 19, 20, 21] := by simp [Scratch] at hk ⊢; omega
        exact (tu k a1).trans ((du k a3).trans ((cu k a4).trans ((wu k a5).trans ((pu k a6).trans (hscr k hk)))))
      have hF24 : MemFrame M4 M6 [(up + 8 * (j + n), up + 8 * (j + n) + 8), (qp + 8 * j, qp + 8 * j + 8)] :=
        dfr.trans tfr (by intro a n' h; simp [Outside] at h ⊢; omega)
      have hF2 : MemFrame M M4 [(up + 8 * j, up + 8 * m)] := by
        have h1 : MemFrame M M3 [(up + 8 * j, up + 8 * m)] := pfr.trans wfr
          (by intro a n' h; simp [Outside] at h ⊢; omega)
        exact h1.trans cfr (by intro a n' h; simp [Outside] at h ⊢; omega)
      have hFa : MemFrame M M5 (LRanges up qp j m) := by
        have h1 : MemFrame M M3 (LRanges up qp j m) := pfr.trans wfr
          (by intro a n' h; simp [LRanges, Outside] at h; simp [Outside]; omega)
        have h2 : MemFrame M M4 (LRanges up qp j m) := h1.trans cfr
          (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)
        exact h2.trans dfr (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)
      have hFb : MemFrame M M6 (LRanges up qp j m) := hFa.trans tfr
        (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)
      have hw64 : Fv256.B.wv M6 (up + 8 * j) n = Fv256.B.wv M4 (up + 8 * j) n :=
        Fv256.B.wv_of_frame M4 M6 _ hF24 (up + 8 * j) n (by simp [Outside]; omega)
      have hqm : qh - 1 = Fv256.B.wv M (up + 8 * j) (n + 1) / Fv256.B.wv M0 dp n := by omega
      refine ⟨R6, fl6, M6, rfl, ?_, ?_, hpres⟩
      · exact ⟨(hpres 0 (by simp [Scratch]) (by omega)).trans r0, (hpres 2 (by simp [Scratch]) (by omega)).trans r2, t3,
          (hpres 4 (by simp [Scratch]) (by omega)).trans r4, (hpres 5 (by simp [Scratch]) (by omega)).trans r5,
          (hpres 6 (by simp [Scratch]) (by omega)).trans r6, (hpres 7 (by simp [Scratch]) (by omega)).trans r7,
          (hpres 8 (by simp [Scratch]) (by omega)).trans r8, (hpres 9 (by simp [Scratch]) (by omega)).trans r9,
          (hpres 10 (by simp [Scratch]) (by omega)).trans r10⟩
      · exact kinv_finish up dp qp n m ql v dl dh cap M0 M M6 s0.sp.toNat j (qh - 1) (Fv256.B.wv M (up + 8 * j) (n + 1) % Fv256.B.wv M0 dp n) K0 hj hI hFb
          (by rw [hw64]; omega) (trd.trans rfl) (by rw [← hqm] at hsum; omega) (Nat.mod_lt _ (by omega))
end Fv256.Arm64.KnuthLoop
