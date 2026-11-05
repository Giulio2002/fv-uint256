import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.Amd64.UdivremA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremC

set_option maxHeartbeats 8000000 in
theorem mid1_pos {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul ≤ L) (hul1 : 1 ≤ ul)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = 0#64) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = BitVec.ofNat 64 s)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - s) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x182))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x145), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x182), flags := fl', mem := M' } ∧
        R' 1 = 0 - BitVec.ofNat 64 (64 - s) ∧ R' 9 = BitVec.ofNat 64 qcap ∧ R' 11 = 0 - BitVec.ofNat 64 (64 - s) ∧
        R' 12 = BitVec.ofNat 64 (ul - 1) ∧ R' 15 = 18446744073709551615#64 ∧
        (∀ k, k ∉ [1, 9, 11, 12, 15] → R' k = R k) ∧
        M'.readLE (sf + 0x98) 8 = (M.readLE dp 8 * 2 ^ s) % 2 ^ 64 ∧ MemFrame M M' [(sf + 0x98, sf + 0x98 + 8)]) := by
  have hcode := ku_lt
  have hnz : ¬ (BitVec.ofNat 64 n) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hsn : ¬ (18446744073709551616 - (64 - s)) % 64 = 0 := by omega
  have hd0 : M.readLE dp 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M dp 8; simpa using this
  janus64_run [hsn, hnz, e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, e2, e6, m_d8, m_f8, m_108, m_100, m_110, m_130]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (simp [setRegF, hs]; done)
    | (simp [setRegF]; bv_omega)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 9 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 15 := by simpa using hk
       obtain ⟨k1, k9, k11, k12, k15⟩ := hk'
       simp [setRegF, k1, k9, k11, k12, k15])
    | (rw [Janus.Arm64.Memory.readLE_writeLE_self]
       rw [show (18446744073709551616 - (64 - s)) % 64 = s by omega]
       have hm : ((if s < 64 then 18446744073709551615#64 else 0#64).toNat) = 2 ^ 64 - 1 := by simp [show s < 64 by omega]
       rw [hm]
       have hx : M.readLE dp 8 * 2 ^ s % 18446744073709551616 < 2 ^ 64 := Nat.mod_lt _ (by decide)
       rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
       simp only [Nat.reducePow]
       exact Nat.mod_eq_of_lt hx)
    | exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x98, sf + 0x98 + 8)) (List.Mem.head _) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem mid1_zero {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul ≤ L) (hul1 : 1 ≤ ul)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = 0#64) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - 0))
    (e8 : R 8 = 0 - BitVec.ofNat 64 0) (e13 : R 13 = BitVec.ofNat 64 (63 - 0)) (e15 : R 15 = BitVec.ofNat 64 0)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - 0) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x182))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x145), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x182), flags := fl', mem := M' } ∧
        R' 1 = 0 - BitVec.ofNat 64 (64 - 0) ∧ R' 9 = BitVec.ofNat 64 qcap ∧ R' 11 = 0 - BitVec.ofNat 64 (64 - 0) ∧
        R' 12 = BitVec.ofNat 64 (ul - 1) ∧ R' 15 = 18446744073709551615#64 ∧
        (∀ k, k ∉ [1, 9, 11, 12, 15] → R' k = R k) ∧
        M'.readLE (sf + 0x98) 8 = (M.readLE dp 8 * 2 ^ 0) % 2 ^ 64 ∧ MemFrame M M' [(sf + 0x98, sf + 0x98 + 8)]) := by
  have hcode := ku_lt
  have hnz : ¬ (BitVec.ofNat 64 n) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  have hd0 : M.readLE dp 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M dp 8; simpa using this
  janus64_run [hnz, e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, e2, e6, m_d8, m_f8, m_108, m_100, m_110, m_130]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (simp [setRegF]; done)
    | (simp [setRegF]; bv_omega)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 9 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 15 := by simpa using hk
       obtain ⟨k1, k9, k11, k12, k15⟩ := hk'
       simp [setRegF, k1, k9, k11, k12, k15])
    | (rw [Janus.Arm64.Memory.readLE_writeLE_self]
       have hx : M.readLE dp 8 * 2 ^ ((18446744073709551616 - (64 - 0)) % 64) % 18446744073709551616 < 2 ^ 64 := Nat.mod_lt _ (by decide)
       simp only [show (18446744073709551616 - (64 - 0)) % 64 = 0 by decide, show (0:Nat) < 64 by decide, if_true] at hx ⊢
       simp [Fv256.B.and_mask, Nat.mod_eq_of_lt hd0])
    | exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x98, sf + 0x98 + 8)) (List.Mem.head _) (by omega) (by omega)


set_option maxHeartbeats 8000000 in
theorem mid1 {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul ≤ L) (hul1 : 1 ≤ ul)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : dp + 32 ≤ sf ∨ sf + 0x138 ≤ dp)
    (e12 : R 12 = 0#64) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = BitVec.ofNat 64 qcap) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = BitVec.ofNat 64 s)
    (e9 : R 9 = BitVec.ofNat 64 dp) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul)
    (m_d8 : M.readLE (sf + 0xd8) 8 = 64 - s) (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (m_108 : M.readLE (sf + 0x108) 8 = qcap)
    (m_100 : M.readLE (sf + 0x100) 8 = ql) (m_110 : M.readLE (sf + 0x110) 8 = up) (m_130 : M.readLE (sf + 0x130) 8 = remp) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x182))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x145), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x182), flags := fl', mem := M' } ∧
        R' 1 = 0 - BitVec.ofNat 64 (64 - s) ∧ R' 9 = BitVec.ofNat 64 qcap ∧ R' 11 = 0 - BitVec.ofNat 64 (64 - s) ∧
        R' 12 = BitVec.ofNat 64 (ul - 1) ∧ R' 15 = 18446744073709551615#64 ∧
        (∀ k, k ∉ [1, 9, 11, 12, 15] → R' k = R k) ∧
        M'.readLE (sf + 0x98) 8 = (M.readLE dp 8 * 2 ^ s) % 2 ^ 64 ∧ MemFrame M M' [(sf + 0x98, sf + 0x98 + 8)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact mid1_zero hL s0 dp qp qcap ql up remp n ul sf R fl M hn hn1 hul hul1 hdp hda hsf hMs hsf0 hdisj e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6 m_d8 m_f8 m_108 m_100 m_110 m_130
  · exact mid1_pos hL s0 dp qp qcap ql up remp n ul s sf R fl M hs h hn hn1 hul hul1 hdp hda hsf hMs hsf0 hdisj e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6 m_d8 m_f8 m_108 m_100 m_110 m_130

-- the search for the most significant non-zero word of `u` (head at +0x182, exit at +0x1a0)
set_option maxHeartbeats 8000000 in
theorem ulen_loop {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up qp : Nat) (M : Memory) (sf : Nat)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true) (hsf : sf + 0x138 ≤ 2 ^ 48) (hsf0 : 0x20 ≤ sf)
    (hMs : M.accessible sf 0x138 true = true) (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up)
    (m_f8 : M.readLE (sf + 0xf8) 8 = qp) (hqp : qp < 2 ^ 64) :
    ∀ t (R : Nat → W64) (fl : Flags), t ≤ L → R 7 = BitVec.ofNat 64 up → R 4 = BitVec.ofNat 64 sf → R 12 = BitVec.ofNat 64 t - 1 →
      R 0 = BitVec.ofNat 64 qp →
      (∀ j, t ≤ j → j < L → M.readLE (up + 8 * j) 8 = 0) →
      ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x1a0))
        { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x182), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (n : Nat),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl', mem := M } ∧
          R' 12 = BitVec.ofNat 64 n ∧ n ≤ t ∧ (∀ j, n ≤ j → j < L → M.readLE (up + 8 * j) 8 = 0) ∧
          (0 < n → M.readLE (up + 8 * (n - 1)) 8 ≠ 0) ∧ R' 0 = BitVec.ofNat 64 qp ∧ (∀ k, k ∉ [0, 12] → R' k = R k)) := by
  intro t
  induction t with
  | zero =>
    intro R fl ht r7 r4 r12 r0 hz
    have hcode := ku_lt
    have hneg : (R 12).msb = true := by rw [r12]; decide
    janus64_run [hneg]
    refine ⟨_, _, 0, rfl, by simp [setRegF], Nat.le_refl _, hz, fun h => absurd h (by omega), by simp [setRegF, r0], ?_⟩
    intro k hk
    have h1 : k ≠ 12 := fun h => hk (by simp [h])
    simp [setRegF, h1]
  | succ t ih =>
    intro R fl ht r7 r4 r12 r0 hz
    have hcode := ku_lt
    have hnn : (R 12).msb = false := by
      rw [r12, BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    have hRt : R 12 = BitVec.ofNat 64 t := by rw [r12]; bv_omega
    have hxt : (R 12).toNat = t := by rw [hRt, BitVec.toNat_ofNat]; omega
    have mq : (BitVec.ofNat 64 qp) = BitVec.ofNat 64 qp := rfl
    by_cases hzero : M.readLE (up + 8 * t) 8 = 0
    · have hzero' : M.readLE (up + t * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hzero
      janus64_run [hnn, hzero', hxt, r7, r4, m_f8] until [ku + 0x182]
      refine Fv256.B.reachesRet_mono64 (ih _ _ (by omega) (by simp [setRegF, r7]) (by simp [setRegF, r4]) (by simp [setRegF, hRt])
        (by simp [setRegF, m_f8]) (fun j hj1 hj2 => by
          by_cases hjt : j = t
          · subst hjt; exact hzero
          · exact hz j (by omega) hj2)) ?_
      rintro S ⟨R', fl', n, hS, h2, hn, hzz, hnz, h0, hk⟩
      refine ⟨R', fl', n, hS, h2, by omega, hzz, hnz, h0, ?_⟩
      intro k hk'
      rw [hk k hk']
      have h1 : k ≠ 0 := fun h => hk' (by simp [h])
      have h12 : k ≠ 12 := fun h => hk' (by simp [h])
      simp [setRegF, h1, h12]
    · have hzero' : ¬ M.readLE (up + t * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hzero
      janus64_run [hnn, hzero', hxt, r7, r4, m_f8]
      refine ⟨_, _, t + 1, rfl, ?_, Nat.le_refl _, fun j hj1 hj2 => hz j (by omega) hj2, fun _ => by simpa using hzero, by simp [setRegF, m_f8], ?_⟩
      · simp [setRegF, hRt]; bv_omega
      · intro k hk'
        have h1 : k ≠ 0 := fun h => hk' (by simp [h])
        have h12 : k ≠ 12 := fun h => hk' (by simp [h])
        simp [setRegF, h1, h12]

end Fv256.Amd64.UdivremC
