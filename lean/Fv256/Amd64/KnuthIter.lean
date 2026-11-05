import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.KnuthSub
import Fv256.Amd64.KnuthEst
import Fv256.Amd64.KnuthOvf

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.KnuthSub

namespace Fv256.Amd64.KnuthIter

-- The estimate stage of one `udivremKnuth` iteration: from the loop head to the multiply-subtract loop.
set_option maxHeartbeats 8000000 in
theorem est_all (s0 : State) (up dp n m j v dl dh u2 u1 u0 : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : 2 ≤ n) (hn2 : n < 2 ^ 20) (hm : j + n + 1 ≤ m) (hm2 : m < 2 ^ 20)
    (hdh : 2 ^ 63 ≤ dh) (hdh2 : dh < 2 ^ 64) (hdl : dl < 2 ^ 64) (hu2B : u2 < 2 ^ 64) (hu1B : u1 < 2 ^ 64) (hu0B : u0 < 2 ^ 64)
    (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / dh)
    (hs : (R 4).toNat + 0x90 ≤ 2 ^ 48)
    (hMs : M.accessible (R 4).toNat 0x90 true = true)
    (hua : M.accessible up (8 * m) true = true) (hub : up + 8 * m ≤ 2 ^ 48)
    (hda : M.accessible dp (8 * n) false = true) (hdb : dp + 8 * n ≤ 2 ^ 48)
    (hsu : up + 8 * m ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ up) (hsd : dp + 8 * n ≤ (R 4).toNat ∨ (R 4).toNat + 0x90 ≤ dp)
    (hcap : m ≤ (R 8).toNat) (hcapB : (R 8).toNat < 2 ^ 55)
    (e0 : R 0 = BitVec.ofNat 64 v) (e6 : R 6 = BitVec.ofNat 64 j) (e7 : R 7 = BitVec.ofNat 64 up) (e9 : R 9 = BitVec.ofNat 64 dp)
    (e10 : R 10 = BitVec.ofNat 64 n) (e11 : R 11 = BitVec.ofNat 64 dl) (e13 : R 13 = BitVec.ofNat 64 m)
    (e15 : R 15 = BitVec.ofNat 64 dh) (e1 : R 1 = BitVec.ofNat 64 (n - 1))
    (hm10 : M.readLE ((R 4).toNat + 0x10) 8 = v) (hm88 : M.readLE ((R 4).toNat + 0x88) 8 = dp) (hm30 : M.readLE ((R 4).toNat + 0x30) 8 = dl)
    (hu2 : M.readLE (up + (j + n) * 8) 8 = u2) (hu1 : M.readLE (up + (j + (n - 1)) * 8) 8 = u1) (hu0 : M.readLE (up + (j + (n - 2)) * 8) 8 = u0) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (kn + 0x235))
      { s0 with regs := R, rip := BitVec.ofNat 64 (kn + 0xd1), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (qh : Nat),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (kn + 0x235), flags := fl', mem := M' } ∧
        qh = Fv256.B.qhat1 (2 ^ 64) dh dl u2 u1 u0 ∧ qh < 2 ^ 64 ∧
        R' 0 = BitVec.ofNat 64 v ∧ R' 1 = BitVec.ofNat 64 (n - 1) ∧ R' 2 = BitVec.ofNat 64 u2 ∧
        R' 3 = BitVec.ofNat 64 qh ∧
        R' 6 = BitVec.ofNat 64 (up + 8 * j) ∧ R' 9 = BitVec.ofNat 64 dp ∧ R' 11 = 0 ∧ R' 12 = BitVec.ofNat 64 m ∧ R' 13 = 0 ∧
        (∀ k, k ∉ [0, 1, 2, 3, 6, 9, 11, 12, 13] → R' k = R k) ∧
        M'.readLE ((R 4).toNat + 0x28) 8 = j ∧ M'.readLE (R 4).toNat 8 = u2 ∧ M'.readLE ((R 4).toNat + 0x38) 8 = j + n ∧
        MemFrame M M' [((R 4).toNat, (R 4).toNat + 0x10), ((R 4).toNat + 0x18, (R 4).toNat + 0x30), ((R 4).toNat + 0x38, (R 4).toNat + 0x40)]) := by
  by_cases hlt : u2 < dh
  · have hr := Fv256.Amd64.KnuthEst.est1 s0 up dp n m j v dl dh u2 u1 u0 R fl M hn hn2 hm hm2 hdh hdh2 hdl hv hs hMs hua hub hda hdb hsu hsd
      hlt hcap e0 e6 e7 e9 e10 e11 e13 e15 e1 hu2 hu1 hu0
    refine Fv256.B.reachesRet_trans64 hr ?_
    intro S' hrip ⟨R1, fl1, M1, hS, q0, q2, q3, q912, qu, m8, m18, m0, m38, mfr⟩
    subst hS
    have hQ : (u2 * 2 ^ 64 + u1) / dh < 2 ^ 64 := by
      apply Nat.div_lt_of_lt_mul
      have : (u2 + 1) * 2 ^ 64 ≤ dh * 2 ^ 64 := Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul] at this
      rw [Nat.mul_comm dh]; omega
    have hrB : (u2 * 2 ^ 64 + u1) % dh < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ (by omega)) hdh2
    have h4 : R1 4 = R 4 := qu 4 (by simp)
    have h8 : R1 8 = R 8 := qu 8 (by simp)
    have hMs1 : M1.accessible (R 4).toNat 0x90 true = true := by rw [mfr.accessible]; exact hMs
    have hua1 : M1.accessible up (8 * m) true = true := by rw [mfr.accessible]; exact hua
    have hda1 : M1.accessible dp (8 * n) false = true := by rw [mfr.accessible]; exact hda
    have hm10' : M1.readLE ((R 4).toNat + 0x10) 8 = v := by rw [mfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hm10
    have hm88' : M1.readLE ((R 4).toNat + 0x88) 8 = dp := by rw [mfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hm88
    have hm30' : M1.readLE ((R 4).toNat + 0x30) 8 = dl := by rw [mfr.readLE _ _ (by simp [Outside] <;> omega)]; exact hm30
    have hm8' : M1.readLE ((R 4).toNat + 8) 8 = (u2 * 2 ^ 64 + u1) % dh := by
      rw [m8, q2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrB]
    have hm18' : M1.readLE ((R 4).toNat + 0x18) 8 = (u2 * 2 ^ 64 + u1) / dh := by
      rw [m18, q0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hQ]
    have hm0' : M1.readLE (R 4).toNat 8 = u2 := m0
    have h2 := Fv256.Amd64.KnuthEst.est2 { s0 with regs := R1, rip := BitVec.ofNat 64 (kn + 0x17d), flags := fl1, mem := M1 }
      up dp n m j v dl dh u2 u0 ((u2 * 2 ^ 64 + u1) / dh) ((u2 * 2 ^ 64 + u1) % dh) R1 fl1 M1 hn hn2 hm hm2 hQ hrB hdl hu0B
      (by rw [h4]; exact hs) (by rw [h4]; exact hMs1) hua1 hub hda1 hdb (by rw [h4]; exact hsu) (by rw [h4]; exact hsd)
      (by rw [h8]; exact hcap) (by rw [h8]; exact hcapB) q0 q2 q3
      (by rw [qu 6 (by simp), e6]) (by rw [qu 7 (by simp), e7]) (by rw [qu 1 (by simp), e1])
      (by rw [qu 10 (by simp), e10]) (by rw [qu 11 (by simp), e11]) (by rw [qu 13 (by simp), e13]) q912
      (by rw [h4]; exact hm8') (by rw [h4]; exact hm18') (by rw [h4]; exact hm0') (by rw [h4]; exact hm10')
      (by rw [h4]; exact hm88') (by rw [h4]; exact hm30')
    refine Fv256.B.reachesRet_mono64 h2 ?_
    intro S2 ⟨R2, fl2, M2, hS2, p0, p1, p2, p3, p6, p9, p11, p12, p13, pu, pj, pfr⟩
    subst hS2
    have hq : Fv256.B.qhat1 (2 ^ 64) dh dl u2 u1 u0 = if ((u2 * 2 ^ 64 + u1) % dh) * 2 ^ 64 + u0 < ((u2 * 2 ^ 64 + u1) / dh) * dl then (u2 * 2 ^ 64 + u1) / dh - 1 else (u2 * 2 ^ 64 + u1) / dh := by
      unfold Fv256.B.qhat1
      rw [if_neg (by omega)]
    have pfr' : MemFrame M1 M2 [((R 4).toNat + 0x28, (R 4).toNat + 0x30)] := by rw [← h4]; exact pfr
    refine ⟨R2, fl2, M2, _, rfl, hq.symm, ?_, p0, p1, p2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · split <;> omega
    · exact p3
    · exact p6
    · exact p9
    · exact p11
    · exact p12
    · exact p13
    · intro k hk
      have hk' : k ∉ [0, 2, 3, 9, 12] := by simp at hk ⊢; omega
      rw [pu k hk, qu k hk']
    · rw [← h4]; exact pj
    · rw [pfr'.readLE _ _ (by simp [Outside] <;> omega)]; exact m0
    · rw [pfr'.readLE _ _ (by simp [Outside] <;> omega)]; exact m38
    · exact mfr.trans pfr' (by intro a n h; simp [Outside] at h ⊢; omega)
  · have hge : dh ≤ u2 := by omega
    refine Fv256.B.reachesRet_mono64 (Fv256.Amd64.KnuthOvf.est_ovf s0 up dp n m j v dl dh u2 u1 u0 R fl M hn hn2 hm hm2 hdh hdh2
      hs hMs hua hub hda hdb hsu hsd hge hu2B hcap hcapB e0 e6 e7 e9 e10 e11 e13 e15 e1 hu2 hu1 hu0) ?_
    intro S2 ⟨R2, fl2, M2, hS2, p0, p1, p2, p3, p6, p9, p11, p12, p13, pu, pj, pm0, pm38, pfr⟩
    subst hS2
    refine ⟨R2, fl2, M2, 2 ^ 64 - 1, rfl, ?_, by omega, p0, p1, p2, p3, p6, p9, p11, p12, p13, pu, pj, pm0, pm38, pfr⟩
    unfold Fv256.B.qhat1
    rw [if_pos hge]


end Fv256.Amd64.KnuthIter
