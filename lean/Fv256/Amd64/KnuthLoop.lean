import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.Amd64.KnuthSub
import Fv256.Amd64.KnuthEst
import Fv256.Amd64.KnuthOvf
import Fv256.Amd64.KnuthIter
import Fv256.Amd64.KnuthAdd
import Fv256.Amd64.KnuthTail
import Fv256.Amd64.KnuthDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub
open Fv256.Amd64.KnuthDefs

namespace Fv256.Amd64.KnuthLoop

set_option maxHeartbeats 8000000 in
theorem iter (s0 : State) (up dp qp n m ql v dl dh cap : Nat) (M0 : Memory) (R : Nat → W64) (sp : W64) (fl : Flags)
    (M : Memory) (j : Nat) (K : KC up dp qp n m ql v dl dh cap sp.toNat M0) (hj : j + n + 1 ≤ m)
    (hR : HeadR R (j + 1) v n m up dp dl dh cap ql sp) (hI : KInv M0 M up dp qp n m sp.toNat (j + 1)) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0xd1))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl', mem := M' } ∧
        HeadR R' j v n m up dp dl dh cap ql sp ∧ KInv M0 M' up dp qp n m sp.toNat j ∧ R' 14 = R 14) := by
  obtain ⟨r0, r1, r3, r4, r6, r7, r8, r9, r10, r11, r13, r15⟩ := hR
  have hfr := hI.fr
  have K0 := K
  obtain ⟨hn, hn2, hm2, hmq, hql2, hdh, hdl, hdh63, hv, hcap, hcapB, hsp, hup, hdp, hqp, hdu, hds, hus, hqu, hqs, hqd, hua, hda, hqa, hsa, s10, s30, s40, s58, s60, s80, s88⟩ := K
  have hqlj : j < ql := by omega
  have hr6 : R 6 = BitVec.ofNat 64 j := by rw [r6]; bv_omega
  have hR4 : (R 4).toNat = sp.toNat := by rw [r4]
  have hcapR : (R 8).toNat = cap := by rw [r8, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  -- the three top words of the window and the memory facts of the estimate stage
  have hu2B := Janus.Arm64.Memory.readLE_lt M (up + (j + n) * 8) 8
  have hu1B := Janus.Arm64.Memory.readLE_lt M (up + (j + (n - 1)) * 8) 8
  have hu0B := Janus.Arm64.Memory.readLE_lt M (up + (j + (n - 2)) * 8) 8
  simp only [Nat.reducePow] at hu2B hu1B hu0B
  have hdlB : dl < 2 ^ 64 := by
    rw [hdl]; have := Janus.Arm64.Memory.readLE_lt M0 (dp + 8 * (n - 2)) 8; simpa using this
  have hdhB : dh < 2 ^ 64 := by
    rw [hdh]; have := Janus.Arm64.Memory.readLE_lt M0 (dp + 8 * (n - 1)) 8; simpa using this
  have hMs : M.accessible sp.toNat 0x90 true = true := by rw [hfr.accessible]; exact hsa
  have hMu : M.accessible up (8 * m) true = true := by rw [hfr.accessible]; exact hua
  have hMd : M.accessible dp (8 * n) false = true := by rw [hfr.accessible]; exact hda
  have hMq : M.accessible qp (8 * ql) true = true := by rw [hfr.accessible]; exact hqa
  have sm10 : M.readLE (sp.toNat + 0x10) 8 = v := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s10
  have sm88 : M.readLE (sp.toNat + 0x88) 8 = dp := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s88
  have sm30 : M.readLE (sp.toNat + 0x30) 8 = dl := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s30
  have sm40 : M.readLE (sp.toNat + 0x40) 8 = n - 1 := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s40
  have sm58 : M.readLE (sp.toNat + 0x58) 8 = qp := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s58
  have sm60 : M.readLE (sp.toNat + 0x60) 8 = ql := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s60
  have sm80 : M.readLE (sp.toNat + 0x80) 8 = cap := by rw [hfr.readLE _ _ (by simp [Outside] <;> omega)]; exact s80
  obtain ⟨u2, hu2⟩ : ∃ u2, M.readLE (up + (j + n) * 8) 8 = u2 := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1, M.readLE (up + (j + (n - 1)) * 8) 8 = u1 := ⟨_, rfl⟩
  obtain ⟨u0, hu0⟩ : ∃ u0, M.readLE (up + (j + (n - 2)) * 8) 8 = u0 := ⟨_, rfl⟩
  rw [hu2] at hu2B
  rw [hu1] at hu1B
  rw [hu0] at hu0B
  have h1 := Fv256.Amd64.KnuthIter.est_all s0 up dp n m j v dl dh u2 u1 u0 R fl M hn hn2 (by omega) hm2 hdh63 hdhB hdlB
    hu2B hu1B hu0B hv (by rw [hR4]; exact hsp) (by rw [hR4]; exact hMs) hMu (by omega) hMd (by omega)
    (by rw [hR4]; exact hus) (by rw [hR4]; exact hds) (by rw [hcapR]; exact hcap) (by rw [hcapR]; exact hcapB)
    r0 hr6 r7 r9 r10 r11 r13 r15 r1 (by rw [hR4]; exact sm10) (by rw [hR4]; exact sm88) (by rw [hR4]; exact sm30) hu2 hu1 hu0
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 hrip ⟨R1, fl1, M1, qh, hS1, hqh, hqhB, q0, q1, q2, q3, q6, q9, q11, q12, q13, qu, qj, qm0, qm38, qfr⟩
  subst hS1
  have hR1_4 : R1 4 = R 4 := qu 4 (by simp)
  have hR1_8 : R1 8 = R 8 := qu 8 (by simp)
  have hsp1 : (R1 4).toNat = sp.toNat := by rw [hR1_4, hR4]
  have hM1a : M1.accessible (up + 8 * j) (8 * n) true = true := by
    rw [qfr.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hMu (by omega) (by omega)
  have hM1d : M1.accessible dp (8 * n) false = true := by rw [qfr.accessible]; exact hMd
  have hM1s : M1.accessible (R1 4).toNat 0x90 true = true := by rw [qfr.accessible, hsp1]; exact hMs
  have hqfr_v : M1.readLE (sp.toNat + 0x10) 8 = v := by rw [qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm10
  have hqfr_c : M1.readLE (sp.toNat + 0x40) 8 = n - 1 := by rw [qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm40
  have hqfr_cap : M1.readLE (sp.toNat + 0x80) 8 = cap := by rw [qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm80
  have h2 := submul_loop { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl1, mem := M1 }
    up dp n j qh (BitVec.ofNat 64 v) (BitVec.ofNat 64 (n - 1)) (BitVec.ofNat 64 u2) (BitVec.ofNat 64 cap) M1 hn hn2 hqhB
    hM1a (by omega) hM1d (by omega) (by omega)
    (by show M1.accessible (R1 4).toNat 0x90 true = true; exact hM1s)
    (by show _ ∨ _; rw [hsp1]; omega) (by show _ ∨ _; rw [hsp1]; omega) (by show (R1 4).toNat + 0x90 ≤ 2 ^ 48; rw [hsp1]; exact hsp)
    (by show M1.readLE ((R1 4).toNat + 0x10) 8 = _; rw [hsp1, hqfr_v, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by have := Fv256.B.recip_lt dh v hdh63 hv; omega)).symm)
    (by show M1.readLE ((R1 4).toNat + 0x40) 8 = _; rw [hsp1, hqfr_c, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm)
    (by show M1.readLE (R1 4).toNat 8 = _; rw [hsp1, ← hR4, qm0, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm)
    (by show M1.readLE ((R1 4).toNat + 0x80) 8 = _; rw [hsp1, hqfr_cap, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm)
    n 0 R1 fl1 M1 (by omega) (qu 10 (by simp) ▸ r10) q11 q3 q6 q9 q0 q1 q2 (by rw [hR1_8]; exact r8)
    (fun k _ => rfl) (by simp [Fv256.B.wv, q13]) (MemFrame.refl _ _)
  refine Fv256.B.reachesRet_trans64 h2 ?_
  intro S2 hrip2 ⟨R2, fl2, M2, hS2, p11, p0, p1, p2, p8, pu, pI, pfr⟩
  subst hS2
  obtain ⟨b, hb⟩ : ∃ b, b = (R2 13).toNat := ⟨_, rfl⟩
  have hbB : b < 2 ^ 64 := by rw [hb]; exact (R2 13).isLt
  have e13 : R2 13 = BitVec.ofNat 64 b := by rw [hb]; simp
  have hR2_4 : R2 4 = sp := by rw [pu 4 (by simp)]; exact (hR1_4.trans r4)
  have hsp2 : (R2 4).toNat = sp.toNat := by rw [hR2_4]
  have hM2a : M2.accessible up (8 * m) true = true := by rw [pfr.accessible, qfr.accessible]; exact hMu
  have hM2q : M2.accessible qp (8 * ql) true = true := by rw [pfr.accessible, qfr.accessible]; exact hMq
  have hM2s : M2.accessible sp.toNat 0x90 true = true := by rw [pfr.accessible, qfr.accessible]; exact hMs
  have hout2 : ∀ a n', (a + n' ≤ up + 8 * j ∨ up + 8 * j + 8 * n ≤ a) → Outside a n' [(up + 8 * j, up + 8 * j + 8 * n)] := by
    intro a n' h; simp [Outside]; omega
  have rm38 : M2.readLE (sp.toNat + 0x38) 8 = j + n := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), ← hR4]; exact qm38
  have rm28 : M2.readLE (sp.toNat + 0x28) 8 = j := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), ← hR4]; exact qj
  have rm60 : M2.readLE (sp.toNat + 0x60) 8 = ql := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm60
  have rm58 : M2.readLE (sp.toNat + 0x58) 8 = qp := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm58
  have rm40 : M2.readLE (sp.toNat + 0x40) 8 = n - 1 := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm40
  have rm30 : M2.readLE (sp.toNat + 0x30) 8 = dl := by
    rw [pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm30
  have hR2_3 : R2 3 = BitVec.ofNat 64 qh := by rw [pu 3 (by simp)]; exact q3
  have hR2_12 : R2 12 = BitVec.ofNat 64 m := by rw [pu 12 (by simp)]; exact q12
  have hR2_7 : R2 7 = BitVec.ofNat 64 up := by rw [pu 7 (by simp)]; exact (qu 7 (by simp)).trans r7
  have hR2_10 : R2 10 = BitVec.ofNat 64 n := by rw [pu 10 (by simp)]; exact (qu 10 (by simp)).trans r10
  have hDeq : Fv256.B.wv M dp n = Fv256.B.wv M0 dp n :=
    Fv256.B.wv_of_frame M0 M _ hfr dp n (by simp [Outside]; omega)
  have hD1 : Fv256.B.wv M1 dp n = Fv256.B.wv M0 dp n :=
    (Fv256.B.wv_of_frame M M1 _ qfr dp n (by simp [Outside]; omega)).trans hDeq
  have hZ1 : Fv256.B.wv M1 (up + 8 * j) n = Fv256.B.wv M (up + 8 * j) n :=
    Fv256.B.wv_of_frame M M1 _ qfr (up + 8 * j) n (by simp [Outside]; omega)
  have hsub : Fv256.B.wv M (up + 8 * j) n + b * 2 ^ (64 * n) = Fv256.B.wv M2 (up + 8 * j) n + qh * Fv256.B.wv M0 dp n := by
    rw [hZ1, hD1, ← hb] at pI; exact pI
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
  by_cases hbu : b ≤ u2
  · rcases hcore with ⟨_, hqq, hrr⟩ | ⟨hlt, _⟩
    · have h3 := Fv256.Amd64.KnuthTail.tail_nb { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl1, mem := M1 }
        up dp qp n m j ql v dl dh cap u2 b qh R2 fl2 M2 hn hn2 (by omega) hm2 hqlj hql2 (by rw [hsp2]; exact hsp)
        (by rw [hsp2]; exact hM2s) hM2a (by omega) hM2q (by omega) (by rw [hsp2]; exact hus) (by rw [hsp2]; exact hqs) hqu
        hbu (by omega) hbB hqhB p2 e13 hR2_3 hR2_12 hR2_7 hR2_10
        (by rw [hsp2]; exact rm38) (by rw [hsp2]; exact rm60) (by rw [hsp2]; exact rm28) (by rw [hsp2]; exact rm58)
        (by rw [hsp2]; exact rm40) (by rw [hsp2]; exact rm30)
      refine Fv256.B.reachesRet_mono64 h3 ?_
      intro S3 ⟨R3, fl3, hS3, t1, t3, t6, t11, t13, tu⟩
      subst hS3
      refine ⟨R3, fl3, _, rfl, ?_, ?_, ?_⟩
      · exact ⟨(tu 0 (by simp)).trans p0, t1, t3, (tu 4 (by simp)).trans hR2_4, t6, (tu 7 (by simp)).trans hR2_7,
          (tu 8 (by simp)).trans p8, (tu 9 (by simp)).trans ((pu 9 (by simp)).trans q9), (tu 10 (by simp)).trans hR2_10,
          t11, t13, (tu 15 (by simp)).trans ((pu 15 (by simp)).trans ((qu 15 (by simp)).trans r15))⟩
      · have hFa : MemFrame M M2 (LRanges up qp sp.toNat j m) := qfr.trans pfr
          (by intro a n' h; simp [LRanges, Outside] at h; simp [Outside]; omega)
        have hFb : MemFrame M (((Janus.Arm64.Memory.writeLE M2 (up + (j + n) * 8) 8 (2 ^ 64 - b + u2))).writeLE (qp + j * 8) 8 qh)
            (LRanges up qp sp.toNat j m) :=
          (hFa.writeLE _ (r := (up + 8 * j, up + 8 * m)) (by simp [LRanges]) (by omega) (by omega)).writeLE _
            (r := (qp + 8 * j, qp + 8 * j + 8)) (by simp [LRanges]) (by omega) (by omega)
        have hw1 : Fv256.B.wv (((Janus.Arm64.Memory.writeLE M2 (up + (j + n) * 8) 8 (2 ^ 64 - b + u2))).writeLE (qp + j * 8) 8 qh)
            (up + 8 * j) n = Fv256.B.wv M2 (up + 8 * j) n := by
          rw [Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
        have hrd : (((Janus.Arm64.Memory.writeLE M2 (up + (j + n) * 8) 8 (2 ^ 64 - b + u2))).writeLE (qp + j * 8) 8 qh).readLE
            (qp + 8 * j) 8 = qh := by
          rw [Nat.mul_comm j 8, Janus.Arm64.Memory.readLE_writeLE_self]; simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt hqhB
        rw [← hqq, ← hrr] at hsum
        exact kinv_finish up dp qp n m ql v dl dh cap M0 M _ sp.toNat j qh _ K0 (by omega) hI hFb hw1 hrd hsum
          (by rw [hrr]; exact Nat.mod_lt _ (by omega))

      · exact (tu 14 (by simp)).trans ((pu 14 (by simp)).trans (qu 14 (by simp)))
    · exact absurd hbu (Nat.not_le.mpr hlt)
  · rcases hcore with ⟨hle, _⟩ | ⟨hlt, hqq, hPle, hrr⟩
    · exact absurd hle hbu
    · have hqh1 : 1 ≤ qh := by rw [hqq]; exact Nat.le_add_left 1 _
      have h3a := Fv256.Amd64.KnuthTail.tail_b1 { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl1, mem := M1 }
        up dp qp n m j ql v dl dh cap u2 b qh R2 fl2 M2 hn hn2 (by omega) hm2 (by rw [hsp2]; exact hsp)
        (by rw [hsp2]; exact hM2s) hM2a (by omega) (by rw [hsp2]; exact hus) hlt (by omega) hbB p2 e13 hR2_7 hR2_10
        (by rw [hsp2]; exact rm38)
      refine Fv256.B.reachesRet_trans64 h3a ?_
      intro S3 hrip3 ⟨R3, fl3, hS3, t1, t2, t11, tu⟩
      subst hS3
      clear hrip3
      generalize hM3a : Janus.Arm64.Memory.writeLE M2 (up + (j + n) * 8) 8 (2 ^ 64 - b + u2) = M3a
      have hR3_4 : R3 4 = sp := (tu 4 (by simp)).trans hR2_4
      have hsp3 : (R3 4).toNat = sp.toNat := by rw [hR3_4]
      have hA3 : ∀ a n' w, M3a.accessible a n' w = M2.accessible a n' w := fun a n' w => by
        rw [← hM3a]; simp [Janus.Arm64.Memory.accessible_writeLE]
      have rd3 : ∀ a n', (a + n' ≤ up + (j + n) * 8 ∨ up + (j + n) * 8 + 8 ≤ a) → M3a.readLE a n' = M2.readLE a n' := fun a n' h => by
        rw [← hM3a]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
      have hR3_6 : R3 6 = BitVec.ofNat 64 (up + 8 * j) := (tu 6 (by simp)).trans ((pu 6 (by simp)).trans q6)
      have hR3_9 : R3 9 = BitVec.ofNat 64 dp := (tu 9 (by simp)).trans ((pu 9 (by simp)).trans q9)
      have hR3_10 : R3 10 = BitVec.ofNat 64 n := (tu 10 (by simp)).trans hR2_10
      have hR3_0 : R3 0 = BitVec.ofNat 64 v := (tu 0 (by simp)).trans p0
      have hR3_8 : R3 8 = BitVec.ofNat 64 cap := (tu 8 (by simp)).trans p8
      have hMa3 : M3a.accessible (up + 8 * j) (8 * n) true = true := by
        rw [hA3]; exact Janus.Arm64.Memory.accessible_mono _ hM2a (by omega) (by omega)
      have hMd3 : M3a.accessible dp (8 * n) false = true := by rw [hA3, pfr.accessible, qfr.accessible]; exact hMd
      have rs10 : M3a.readLE (sp.toNat + 0x10) 8 = v := by
        rw [rd3 _ _ (by omega), pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm10
      have rs80 : M3a.readLE (sp.toNat + 0x80) 8 = cap := by
        rw [rd3 _ _ (by omega), pfr.readLE _ _ (by simp [Outside] <;> omega), qfr.readLE _ _ (by simp [Outside] <;> omega)]; exact sm80
      have h4 := Fv256.Amd64.KnuthAdd.addback_loop
        { { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl1, mem := M1 } with regs := R3, rip := BitVec.ofNat 64 (kn + 0x2a2), flags := fl3, mem := M3a }
        up dp n j (BitVec.ofNat 64 v) (BitVec.ofNat 64 cap) M3a hn hn2 hMa3 (by omega) hMd3 (by omega) (by omega)
        (by show M3a.accessible (R3 4).toNat 0x90 true = true; rw [hsp3, hA3]; exact hM2s)
        (by show _ ∨ _; rw [hsp3]; omega) (by show _ ∨ _; rw [hsp3]; omega) (by show (R3 4).toNat + 0x90 ≤ 2 ^ 48; rw [hsp3]; exact hsp)
        (by show M3a.readLE ((R3 4).toNat + 0x10) 8 = _; rw [hsp3, rs10, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by have := Fv256.B.recip_lt dh v hdh63 hv; omega)).symm)
        (by show M3a.readLE ((R3 4).toNat + 0x80) 8 = _; rw [hsp3, rs80, BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by omega)).symm)
        n 0 0 R3 fl3 M3a (by omega) (by omega) hR3_10 (by rw [t2]; rfl) (by rw [t11]; rfl) hR3_6 hR3_9 hR3_0 hR3_8
        (fun k _ => rfl) (by simp [Fv256.B.wv]) (MemFrame.refl _ _)
      refine Fv256.B.reachesRet_trans64 h4 ?_
      intro S4 hrip4 ⟨R4, fl4, M4, c', hS4, hc', c11, c0, c8, c2, cu, cI, cfr⟩
      subst hS4
      have hw3 : Fv256.B.wv M3a (up + 8 * j) n = Fv256.B.wv M2 (up + 8 * j) n := by
        rw [← hM3a]; exact Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)
      have hd3 : Fv256.B.wv M3a dp n = Fv256.B.wv M0 dp n := by
        rw [← hM3a, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
          Fv256.B.wv_of_frame M1 M2 _ pfr dp n (by simp [Outside]; omega), hD1]
      rw [hw3, hd3] at cI
      have hW4lt := Fv256.B.wv_lt M4 (up + 8 * j) n
      have hc1 : c' = 1 := by
        rcases (show c' = 0 ∨ c' = 1 by omega) with h | h
        · rw [h] at cI; omega
        · exact h
      subst hc1
      have hR4_4 : R4 4 = sp := (cu 4 (by simp)).trans hR3_4
      have hsp4 : (R4 4).toNat = sp.toNat := by rw [hR4_4]
      have hR4_7 : R4 7 = BitVec.ofNat 64 up := (cu 7 (by simp)).trans ((tu 7 (by simp)).trans hR2_7)
      have hR4_10 : R4 10 = BitVec.ofNat 64 n := (cu 10 (by simp)).trans hR3_10
      have hR4_1 : R4 1 = BitVec.ofNat 64 (j + n) := (cu 1 (by simp)).trans t1
      have hR4_3 : R4 3 = BitVec.ofNat 64 qh := (cu 3 (by simp)).trans ((tu 3 (by simp)).trans hR2_3)
      have hR4_12 : R4 12 = BitVec.ofNat 64 m := (cu 12 (by simp)).trans ((tu 12 (by simp)).trans hR2_12)
      have hMs4 : M4.accessible sp.toNat 0x90 true = true := by rw [cfr.accessible, hA3]; exact hM2s
      have hMu4 : M4.accessible up (8 * m) true = true := by rw [cfr.accessible, hA3]; exact hM2a
      have hMq4 : M4.accessible qp (8 * ql) true = true := by rw [cfr.accessible, hA3]; exact hM2q
      have rq60 : M4.readLE (sp.toNat + 0x60) 8 = ql := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega), rd3 _ _ (by omega)]; exact rm60
      have rq28 : M4.readLE (sp.toNat + 0x28) 8 = j := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega), rd3 _ _ (by omega)]; exact rm28
      have rq58 : M4.readLE (sp.toNat + 0x58) 8 = qp := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega), rd3 _ _ (by omega)]; exact rm58
      have rq40 : M4.readLE (sp.toNat + 0x40) 8 = n - 1 := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega), rd3 _ _ (by omega)]; exact rm40
      have rq30 : M4.readLE (sp.toNat + 0x30) 8 = dl := by rw [cfr.readLE _ _ (by simp [Outside] <;> omega), rd3 _ _ (by omega)]; exact rm30
      have h5 := Fv256.Amd64.KnuthTail.tail_b2
        { { { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x235), flags := fl1, mem := M1 } with regs := R3, rip := BitVec.ofNat 64 (kn + 0x2a2), flags := fl3, mem := M3a } with regs := R4, rip := BitVec.ofNat 64 (kn + 0x2a7), flags := fl4, mem := M4 }
        up dp qp n m j ql v dl dh cap qh 1 R4 fl4 M4 hn hn2 (by omega) hm2 hqlj hql2 (by rw [hsp4]; exact hsp) (by rw [hsp4]; exact hMs4)
        hMu4 (by omega) hMq4 (by omega) (by rw [hsp4]; exact hus) (by rw [hsp4]; exact hqs) hqu (Nat.le_refl 1) hqhB hqh1
        hR4_1 c11 hR4_3 hR4_12 hR4_7 hR4_10 (by rw [hsp4]; exact rq60) (by rw [hsp4]; exact rq28) (by rw [hsp4]; exact rq58)
        (by rw [hsp4]; exact rq40) (by rw [hsp4]; exact rq30)
      refine Fv256.B.reachesRet_mono64 h5 ?_
      intro S5 ⟨R5, fl5, hS5, f1, f3, f6, f11, f13, fu⟩
      subst hS5
      refine ⟨R5, fl5, _, rfl, ?_, ?_, ?_⟩
      · exact ⟨(fu 0 (by simp)).trans c0, f1, f3, (fu 4 (by simp)).trans hR4_4, f6, (fu 7 (by simp)).trans hR4_7,
          (fu 8 (by simp)).trans c8, (fu 9 (by simp)).trans ((cu 9 (by simp)).trans hR3_9), (fu 10 (by simp)).trans hR4_10,
          f11, f13, (fu 15 (by simp)).trans ((cu 15 (by simp)).trans ((tu 15 (by simp)).trans ((pu 15 (by simp)).trans ((qu 15 (by simp)).trans r15))))⟩
      · have hFa : MemFrame M M2 (LRanges up qp sp.toNat j m) := qfr.trans pfr
          (by intro a n' h; simp [LRanges, Outside] at h; simp [Outside]; omega)
        have hF3 : MemFrame M M3a (LRanges up qp sp.toNat j m) := by
          rw [← hM3a]
          exact hFa.writeLE _ (r := (up + 8 * j, up + 8 * m)) (by simp [LRanges]) (by omega) (by omega)
        have hF4 : MemFrame M M4 (LRanges up qp sp.toNat j m) := hF3.trans cfr
          (by intro a n' h; simp [LRanges, Outside] at h ⊢; omega)
        have hFb : MemFrame M ((M4.writeLE (up + (j + n) * 8) 8 (M4.readLE (up + (j + n) * 8) 8 + 1)).writeLE (qp + j * 8) 8 (qh - 1))
            (LRanges up qp sp.toNat j m) :=
          (hF4.writeLE _ (r := (up + 8 * j, up + 8 * m)) (by simp [LRanges]) (by omega) (by omega)).writeLE _
            (r := (qp + 8 * j, qp + 8 * j + 8)) (by simp [LRanges]) (by omega) (by omega)
        have hw1 : Fv256.B.wv ((M4.writeLE (up + (j + n) * 8) 8 (M4.readLE (up + (j + n) * 8) 8 + 1)).writeLE (qp + j * 8) 8 (qh - 1))
            (up + 8 * j) n = Fv256.B.wv M (up + 8 * j) (n + 1) % Fv256.B.wv M0 dp n := by
          rw [Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]
          omega
        have hrd : ((M4.writeLE (up + (j + n) * 8) 8 (M4.readLE (up + (j + n) * 8) 8 + 1)).writeLE (qp + j * 8) 8 (qh - 1)).readLE
            (qp + 8 * j) 8 = qh - 1 := by
          rw [Nat.mul_comm j 8, Janus.Arm64.Memory.readLE_writeLE_self]; simp only [Nat.reducePow]
          exact Nat.mod_eq_of_lt (by omega)
        have hqm : qh - 1 = Fv256.B.wv M (up + 8 * j) (n + 1) / Fv256.B.wv M0 dp n := by omega
        exact kinv_finish up dp qp n m ql v dl dh cap M0 M _ sp.toNat j _ _ K0 (by omega) hI hFb hw1 (hrd.trans hqm) hsum
          (Nat.mod_lt _ (by omega))
      · exact (fu 14 (by simp)).trans ((cu 14 (by simp)).trans ((tu 14 (by simp)).trans ((pu 14 (by simp)).trans (qu 14 (by simp)))))

end Fv256.Amd64.KnuthLoop
