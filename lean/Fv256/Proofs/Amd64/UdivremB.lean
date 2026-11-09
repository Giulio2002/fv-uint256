import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.KnuthMathB
import Fv256.Proofs.Common.UdivMathB
import Fv256.Proofs.Amd64.UdivremA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremB

set_option maxHeartbeats 8000000 in
theorem dn_iter_pos (s0 : State) (dp qp qcap ql up remp n ul s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs1 : 1 ≤ s) (hs : s ≤ 63) (hi : i + 1 < n) (hn : n ≤ 4)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = BitVec.ofNat 64 (i + 1)) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = BitVec.ofNat 64 s) (hsn1 : ¬ (18446744073709551616 - s) % 64 = 0) (hsn2 : ¬ (18446744073709551616 - (64 - s)) % 64 = 0)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - s) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x140))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x140), flags := fl, mem := M } (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x140), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x98 + 8 * (i + 1)) 8 = (M.readLE (dp + 8 * (i + 1)) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (dp + 8 * i) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0x98 + 8 * (i + 1), sf + 0x98 + 8 * (i + 1) + 8)]) := by
  have hcode := ku_lt
  have hmsb : (BitVec.ofNat 64 (i + 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hpos : ¬ (BitVec.ofNat 64 (i + 1)) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hsn1, hsn2, hmsb, hpos, e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, m_d8, m_f8, m_108, m_100, m_110, m_130] until [ku + 0x140]
  have hdB : ∀ k, k ≤ 3 → M.readLE (dp + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (dp + 8 * k) 8; simpa using this
  have hda1 := hdB (i + 1) (by omega)
  have hdb1 := hdB i (by omega)
  simp only [Nat.reducePow] at hda1 hdb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · intro k hk
    by_cases k0 : k = 0
    · subst k0; simp [setRegF, e0]
    by_cases k1 : k = 1
    · subst k1; simp [setRegF, e1]
    by_cases k3 : k = 3
    · subst k3; simp [setRegF, e3]
    by_cases k7 : k = 7
    · subst k7; simp [setRegF, e7]
    by_cases k10 : k = 10
    · subst k10; simp [setRegF, e10]
    by_cases k11 : k = 11
    · subst k11; simp [setRegF, e11]
    simp [setRegF, hk, k0, k1, k3, k7, k10, k11]
  · rw [show sf + (i + 1) * 8 + 152 = sf + 152 + 8 * (i + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show dp + (i + 1) * 8 - 8 = dp + 8 * i by omega, show dp + (i + 1) * 8 = dp + 8 * (i + 1) by omega]
    rw [Fv256.B.funnel_mach _ _ s hs1 hs hda1 hdb1]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (Fv256.B.shl_carry_lt _ _ s (by omega) hdb1)
  · exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x98 + 8 * (i + 1), sf + 0x98 + 8 * (i + 1) + 8)) (List.Mem.head _) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem dn_iter_zero (s0 : State) (dp qp qcap ql up remp n ul sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hi : i + 1 < n) (hn : n ≤ 4)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = BitVec.ofNat 64 (i + 1)) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - 0))
    (e8 : R 8 = 0 - BitVec.ofNat 64 0) (e13 : R 13 = BitVec.ofNat 64 (63 - 0)) (e15 : R 15 = BitVec.ofNat 64 0)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - 0) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x140))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x140), flags := fl, mem := M } (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x140), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x98 + 8 * (i + 1)) 8 = (M.readLE (dp + 8 * (i + 1)) 8 * 2 ^ 0) % 2 ^ 64 + M.readLE (dp + 8 * i) 8 / 2 ^ (64 - 0) ∧
        MemFrame M M' [(sf + 0x98 + 8 * (i + 1), sf + 0x98 + 8 * (i + 1) + 8)]) := by
  have hcode := ku_lt
  have hmsb : (BitVec.ofNat 64 (i + 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hpos : ¬ (BitVec.ofNat 64 (i + 1)) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hmsb, hpos, e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, m_d8, m_f8, m_108, m_100, m_110, m_130] until [ku + 0x140]
  have hdB : ∀ k, k ≤ 3 → M.readLE (dp + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (dp + 8 * k) 8; simpa using this
  have hda1 := hdB (i + 1) (by omega)
  have hdb1 := hdB i (by omega)
  simp only [Nat.reducePow] at hda1 hdb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · intro k hk
    by_cases k0 : k = 0
    · subst k0; simp [setRegF, e0]
    by_cases k1 : k = 1
    · subst k1; simp [setRegF, e1]
    by_cases k3 : k = 3
    · subst k3; simp [setRegF, e3]
    by_cases k7 : k = 7
    · subst k7; simp [setRegF, e7]
    by_cases k10 : k = 10
    · subst k10; simp [setRegF, e10]
    by_cases k11 : k = 11
    · subst k11; simp [setRegF, e11]
    simp [setRegF, hk, k0, k1, k3, k7, k10, k11]
  · rw [show sf + (i + 1) * 8 + 152 = sf + 152 + 8 * (i + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show dp + (i + 1) * 8 - 8 = dp + 8 * i by omega, show dp + (i + 1) * 8 = dp + 8 * (i + 1) by omega]
    simp [Fv256.B.and_mask, Nat.div_eq_of_lt hdb1, Nat.mod_eq_of_lt hda1]
  · exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x98 + 8 * (i + 1), sf + 0x98 + 8 * (i + 1) + 8)) (List.Mem.head _) (by omega) (by omega)


theorem dn_iter (s0 : State) (dp qp qcap ql up remp n ul s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hi : i + 1 < n) (hn : n ≤ 4)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = BitVec.ofNat 64 (i + 1)) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = BitVec.ofNat 64 s)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - s) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x140))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x140), flags := fl, mem := M } (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x140), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x98 + 8 * (i + 1)) 8 = (M.readLE (dp + 8 * (i + 1)) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (dp + 8 * i) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0x98 + 8 * (i + 1), sf + 0x98 + 8 * (i + 1) + 8)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact dn_iter_zero s0 dp qp qcap ql up remp n ul sf i R fl M hi hn hdp hda hsf hMs hsf0 hdisj e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 m_d8 m_f8 m_108 m_100 m_110 m_130
  · exact dn_iter_pos s0 dp qp qcap ql up remp n ul s sf i R fl M h hs hi hn hdp hda hsf hMs hsf0 hdisj e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 (by omega) (by omega) e9 e4 m_d8 m_f8 m_108 m_100 m_110 m_130

set_option maxHeartbeats 8000000 in
theorem dn_loop (s0 : State) (dp qp qcap ql up remp n ul s sf : Nat)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n)
    (hdp : dp + 32 ≤ 2 ^ 48) (hsf : sf + 0x138 ≤ 2 ^ 48) (hsf0 : 0x20 ≤ sf) (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp) :
    ∀ i, i < n → ∀ (R : Nat → W64) (fl : Flags) (M : Memory), M.accessible dp 32 false = true → M.accessible sf 0x138 true = true →
      R 12 = BitVec.ofNat 64 i → R 0 = BitVec.ofNat 64 qp → R 1 = BitVec.ofNat 64 qcap → R 3 = BitVec.ofNat 64 ql →
      R 7 = BitVec.ofNat 64 up → R 10 = BitVec.ofNat 64 remp → R 11 = BitVec.ofNat 64 (64 - s) →
      R 8 = 0 - BitVec.ofNat 64 s → R 13 = BitVec.ofNat 64 (63 - s) → R 15 = BitVec.ofNat 64 s →
      R 9 = BitVec.ofNat 64 dp → R 4 = BitVec.ofNat 64 sf →
      M.readLE (sf + 0xd8) 8 = 64 - s → M.readLE (sf + 0xf8) 8 = qp → M.readLE (sf + 0x108) 8 = qcap →
      M.readLE (sf + 0x100) 8 = ql → M.readLE (sf + 0x110) 8 = up → M.readLE (sf + 0x130) 8 = remp →
      (∀ k, i < k → k < n → M.readLE (sf + 0x98 + 8 * k) 8 =
        (M.readLE (dp + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (dp + 8 * (k - 1)) 8 / 2 ^ (64 - s)) →
      ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x145))
        { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x140), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x145), flags := fl', mem := M' } ∧
          R' 12 = 0#64 ∧ (∀ k, k ≠ 12 → R' k = R k) ∧
          (∀ k, 1 ≤ k → k < n → M'.readLE (sf + 0x98 + 8 * k) 8 =
            (M.readLE (dp + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (dp + 8 * (k - 1)) 8 / 2 ^ (64 - s)) ∧
          MemFrame M M' [(sf + 0x98 + 8, sf + 0x98 + 8 * (i + 1))]) := by
  intro i
  induction i with
  | zero =>
    intro hi R fl M hda hMs e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 m_d8 m_f8 m_108 m_100 m_110 m_130 hinv
    have hcode := ku_lt
    have hz : R 12 = 0#64 := e12
    janus64_run [hz]
    refine ⟨_, _, M, rfl, by simp [hz], fun k _ => rfl, fun k hk1 hk2 => hinv k hk1 hk2, MemFrame.refl _ _⟩
  | succ i ih =>
    intro hi R fl M hda hMs e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 m_d8 m_f8 m_108 m_100 m_110 m_130 hinv
    have h1 := dn_iter s0 dp qp qcap ql up remp n ul s sf i R fl M hs hi hn hdp hda hsf hMs hsf0 hdisj e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4
      m_d8 m_f8 m_108 m_100 m_110 m_130
    refine Fv256.B.reachesRet_trans64 h1 ?_
    intro S1 hrip ⟨R1, fl1, M1, hS1, f12, fk, fmem, ffr⟩
    subst hS1
    have hdw : ∀ k, k ≤ 3 → M1.readLE (dp + 8 * k) 8 = M.readLE (dp + 8 * k) 8 := fun k hk =>
      ffr.readLE _ _ (by simp [Outside]; omega)
    have hsl : ∀ a, (a + 8 ≤ sf + 0x98 + 8 * (i + 1) ∨ sf + 0x98 + 8 * (i + 1) + 8 ≤ a) → M1.readLE a 8 = M.readLE a 8 := fun a h =>
      ffr.readLE _ _ (by simp [Outside]; omega)
    have h2 := ih (by omega) R1 fl1 M1 (by rw [ffr.accessible]; exact hda) (by rw [ffr.accessible]; exact hMs) f12
      ((fk 0 (by omega)).trans e0) ((fk 1 (by omega)).trans e1) ((fk 3 (by omega)).trans e3) ((fk 7 (by omega)).trans e7)
      ((fk 10 (by omega)).trans e10) ((fk 11 (by omega)).trans e11) ((fk 8 (by omega)).trans e8) ((fk 13 (by omega)).trans e13)
      ((fk 15 (by omega)).trans e15) ((fk 9 (by omega)).trans e9) ((fk 4 (by omega)).trans e4)
      (by rw [hsl _ (by omega)]; exact m_d8) (by rw [hsl _ (by omega)]; exact m_f8) (by rw [hsl _ (by omega)]; exact m_108)
      (by rw [hsl _ (by omega)]; exact m_100) (by rw [hsl _ (by omega)]; exact m_110) (by rw [hsl _ (by omega)]; exact m_130)
      (by
        intro k hk1 hk2
        rw [hdw k (by omega), hdw (k - 1) (by omega)]
        by_cases hk : k = i + 1
        · subst hk; exact fmem
        · rw [hsl _ (by omega)]; exact hinv k (by omega) hk2)
    refine Fv256.B.reachesRet_mono64 h2 ?_
    rintro S2 ⟨R2, fl2, M2, hS2, g12, gk, gmem, gfr⟩
    refine ⟨R2, fl2, M2, hS2, g12, fun k hk => (gk k hk).trans (fk k hk), fun k hk1 hk2 => ?_, ?_⟩
    · rw [gmem k hk1 hk2, hdw k (by omega), hdw (k - 1) (by omega)]
    · exact ffr.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)

end Fv256.Amd64.UdivremB
