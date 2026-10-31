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

namespace Fv256.Amd64.UdivremF

set_option maxHeartbeats 8000000 in
theorem den_iter_pos (s0 : State) (remp n ulen s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hi : i + 1 < n) (hn : n ≤ 4) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e9 : R 9 = BitVec.ofNat 64 i) (e2 : R 2 = BitVec.ofNat 64 remp) (e3 : R 3 = BitVec.ofNat 64 (n - 1))
    (e0 : R 0 = 18446744073709551615#64) (e6 : R 6 = BitVec.ofNat 64 (ulen + 1)) (e7 : R 7 = 18446744073709551615#64)
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s)) (e4 : R 4 = BitVec.ofNat 64 sf)
    (hsn1 : ¬ (18446744073709551616 - (64 - s)) % 64 = 0) (hsn2 : ¬ (18446744073709551616 - s) % 64 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x3c0))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl, mem := M } (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl', mem := M' } ∧
        R' 9 = BitVec.ofNat 64 (i + 1) ∧ (∀ k, k ∉ [9, 10, 11, 12, 13] → R' k = R k) ∧
        M'.readLE (remp + 8 * i) 8 = M.readLE (sf + 0x48 + 8 * i) 8 / 2 ^ s + (M.readLE (sf + 0x48 + 8 * (i + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64 ∧
        MemFrame M M' [(remp + 8 * i, remp + 8 * i + 8)]) := by
  have hcode := ku_lt
  janus64_run [hsn1, hsn2, e9, e2, e3, e0, e6, e7, e8, e1, e4] until [ku + 0x3c0]
  have hdB : ∀ k, k ≤ 4 → M.readLE (sf + 0x48 + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (sf + 0x48 + 8 * k) 8; simpa using this
  have ha1 := hdB i (by omega)
  have hb1 := hdB (i + 1) (by omega)
  simp only [Nat.reducePow] at ha1 hb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · intro k hk
    have hk' : k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
    by_cases k1 : k = 1
    · subst k1; simp [setRegF, e1]
    · simp [setRegF, k1, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2]
  · rw [show remp + i * 8 = remp + 8 * i by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show sf + i * 8 + 72 = sf + 0x48 + 8 * i by omega, show sf + i * 8 + 80 = sf + 0x48 + 8 * (i + 1) by omega]
    rw [Fv256.B.shr_mach _ _ s hs1 hs ha1 hb1]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (by
      have := Fv256.B.shl_carry_lt (M.readLE (sf + 0x48 + 8 * (i + 1)) 8) (M.readLE (sf + 0x48 + 8 * i) 8) (64 - s) (by omega) ha1
      rw [show 64 - (64 - s) = s by omega] at this
      simp only [Nat.reducePow] at this ⊢
      omega)
  · exact Janus.MemFrame.of_writeLE M _ (r := (remp + 8 * i, remp + 8 * i + 8)) (List.Mem.head _) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem den_iter_zero (s0 : State) (remp n ulen sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hi : i + 1 < n) (hn : n ≤ 4) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e9 : R 9 = BitVec.ofNat 64 i) (e2 : R 2 = BitVec.ofNat 64 remp) (e3 : R 3 = BitVec.ofNat 64 (n - 1))
    (e0 : R 0 = 18446744073709551615#64) (e6 : R 6 = BitVec.ofNat 64 (ulen + 1)) (e7 : R 7 = 0#64)
    (e8 : R 8 = 0 - BitVec.ofNat 64 0) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - 0)) (e4 : R 4 = BitVec.ofNat 64 sf) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x3c0))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl, mem := M } (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl', mem := M' } ∧
        R' 9 = BitVec.ofNat 64 (i + 1) ∧ (∀ k, k ∉ [9, 10, 11, 12, 13] → R' k = R k) ∧
        M'.readLE (remp + 8 * i) 8 = M.readLE (sf + 0x48 + 8 * i) 8 / 2 ^ 0 + (M.readLE (sf + 0x48 + 8 * (i + 1)) 8 * 2 ^ (64 - 0)) % 2 ^ 64 ∧
        MemFrame M M' [(remp + 8 * i, remp + 8 * i + 8)]) := by
  have hcode := ku_lt
  janus64_run [e9, e2, e3, e0, e6, e7, e8, e1, e4] until [ku + 0x3c0]
  have hdB : ∀ k, k ≤ 4 → M.readLE (sf + 0x48 + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (sf + 0x48 + 8 * k) 8; simpa using this
  have ha1 := hdB i (by omega)
  have hb1 := hdB (i + 1) (by omega)
  simp only [Nat.reducePow] at ha1 hb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · intro k hk
    have hk' : k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 11 ∧ k ≠ 12 ∧ k ≠ 13 := by simpa using hk
    by_cases k1 : k = 1
    · subst k1; simp [setRegF, e1]
    · simp [setRegF, k1, hk'.1, hk'.2.1, hk'.2.2.1, hk'.2.2.2.1, hk'.2.2.2.2]
  · rw [show remp + i * 8 = remp + 8 * i by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show sf + i * 8 + 72 = sf + 0x48 + 8 * i by omega, show sf + i * 8 + 80 = sf + 0x48 + 8 * (i + 1) by omega]
    simp [Fv256.B.and_mask, Nat.mod_eq_of_lt ha1]
  · exact Janus.MemFrame.of_writeLE M _ (r := (remp + 8 * i, remp + 8 * i + 8)) (List.Mem.head _) (by omega) (by omega)


set_option maxHeartbeats 8000000 in
theorem den_iter (s0 : State) (remp n ulen s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hi : i + 1 < n) (hn : n ≤ 4) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e9 : R 9 = BitVec.ofNat 64 i) (e2 : R 2 = BitVec.ofNat 64 remp) (e3 : R 3 = BitVec.ofNat 64 (n - 1))
    (e0 : R 0 = 18446744073709551615#64) (e6 : R 6 = BitVec.ofNat 64 (ulen + 1)) (e7 : R 7 = (if s = 0 then 0#64 else 18446744073709551615#64))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s)) (e4 : R 4 = BitVec.ofNat 64 sf) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x3c0))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl', mem := M' } ∧
        R' 9 = BitVec.ofNat 64 (i + 1) ∧ (∀ k, k ∉ [9, 10, 11, 12, 13] → R' k = R k) ∧
        M'.readLE (remp + 8 * i) 8 = M.readLE (sf + 0x48 + 8 * i) 8 / 2 ^ s + (M.readLE (sf + 0x48 + 8 * (i + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64 ∧
        MemFrame M M' [(remp + 8 * i, remp + 8 * i + 8)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact den_iter_zero s0 remp n ulen sf i R fl M hi hn hulen hulen2 hrem hra hsf hMs hsf0 hdisj e9 e2 e3 e0 e6 (by simpa using e7) e8 e1 e4
  · have hne : s ≠ 0 := Nat.pos_iff_ne_zero.mp h
    exact den_iter_pos s0 remp n ulen s sf i R fl M hs h hi hn hulen hulen2 hrem hra hsf hMs hsf0 hdisj e9 e2 e3 e0 e6 (by simpa [hne] using e7) e8 e1 e4 (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem den_loop (s0 : State) (remp n ulen s sf : Nat) (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hsf : sf + 0x140 ≤ 2 ^ 48) (hsf0 : 0x20 ≤ sf) (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp) :
    ∀ t i, i + t = n - 1 → ∀ (R : Nat → W64) (fl : Flags) (M : Memory), M.accessible remp 32 true = true → M.accessible sf 0x140 true = true →
      R 9 = BitVec.ofNat 64 i → R 2 = BitVec.ofNat 64 remp → R 3 = BitVec.ofNat 64 (n - 1) →
      R 0 = 18446744073709551615#64 → R 6 = BitVec.ofNat 64 (ulen + 1) → R 7 = (if s = 0 then 0#64 else 18446744073709551615#64) →
      R 8 = 0 - BitVec.ofNat 64 s → R 1 = 0 - BitVec.ofNat 64 (64 - s) → R 4 = BitVec.ofNat 64 sf →
      ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x3db))
        { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x3db), flags := fl', mem := M' } ∧
          R' 9 = BitVec.ofNat 64 (n - 1) ∧ (∀ k, k ∉ [9, 10, 11, 12, 13] → R' k = R k) ∧
          (∀ j, i ≤ j → j < n - 1 → M'.readLE (remp + 8 * j) 8 =
            M.readLE (sf + 0x48 + 8 * j) 8 / 2 ^ s + (M.readLE (sf + 0x48 + 8 * (j + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64) ∧
          MemFrame M M' [(remp + 8 * i, remp + 8 * (n - 1))]) := by
  intro t
  induction t with
  | zero =>
    intro i hit R fl M hra hMs e9 e2 e3 e0 e6 e7 e8 e1 e4
    have hcode := ku_lt
    have hi : i = n - 1 := by omega
    subst hi
    janus64_run [e9, e3]
    exact ⟨_, _, M, rfl, by simp [e9], fun k _ => rfl, fun j h1 h2 => by omega, MemFrame.refl _ _⟩
  | succ t ih =>
    intro i hit R fl M hra hMs e9 e2 e3 e0 e6 e7 e8 e1 e4
    have h1 := den_iter s0 remp n ulen s sf i R fl M hs (by omega) hn hulen hulen2 hrem hra hsf hMs hsf0 hdisj e9 e2 e3 e0 e6 e7 e8 e1 e4
    refine Fv256.B.reachesRet_trans64 h1 ?_
    intro S1 hrip ⟨R1, fl1, M1, hS1, f9, fk, fmem, ffr⟩
    subst hS1
    have hsl : ∀ a, (a + 8 ≤ remp + 8 * i ∨ remp + 8 * i + 8 ≤ a) → M1.readLE a 8 = M.readLE a 8 := fun a h =>
      ffr.readLE _ _ (by simp [Outside]; omega)
    have hun : ∀ k, k ≤ 4 → M1.readLE (sf + 0x48 + 8 * k) 8 = M.readLE (sf + 0x48 + 8 * k) 8 := fun k hk =>
      hsl _ (by omega)
    have h2 := ih (i + 1) (by omega) R1 fl1 M1 (by rw [ffr.accessible]; exact hra) (by rw [ffr.accessible]; exact hMs) f9
      ((fk 2 (by simp)).trans e2) ((fk 3 (by simp)).trans e3) ((fk 0 (by simp)).trans e0) ((fk 6 (by simp)).trans e6)
      ((fk 7 (by simp)).trans e7) ((fk 8 (by simp)).trans e8) ((fk 1 (by simp)).trans e1) ((fk 4 (by simp)).trans e4)
    refine Fv256.B.reachesRet_mono64 h2 ?_
    rintro S2 ⟨R2, fl2, M2, hS2, g9, gk, gmem, gfr⟩
    refine ⟨R2, fl2, M2, hS2, g9, fun k hk => (gk k hk).trans (fk k hk), fun j hj1 hj2 => ?_, ?_⟩
    · by_cases hji : j = i
      · subst hji
        rw [gfr.readLE _ _ (by simp [Outside]; omega)]; exact fmem
      · rw [gmem j (by omega) hj2, hun j (by omega), hun (j + 1) (by omega)]
    · exact ffr.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)

set_option maxHeartbeats 8000000 in
theorem den_setup (s0 : State) (remp n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hulen : ulen ≤ 4) (hremne : remp ≠ 0) (hremB : remp < 2 ^ 64)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_130 : M.readLE (sf + 0x130) 8 = remp) (m_d0 : M.readLE (sf + 0xd0) 8 = 18446744073709551615)
    (m_e0 : M.readLE (sf + 0xe0) 8 = n - 1) (m_90 : M.readLE (sf + 0x90) 8 = ulen + 1)
    (m_c0 : M.readLE (sf + 0xc0) 8 = (if s = 0 then 0 else 18446744073709551615))
    (m_c8 : M.readLE (sf + 0xc8) 8 = (18446744073709551616 - s) % 2 ^ 64) (m_d8 : M.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - s)) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x3c0))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x2e5), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x3c0), flags := fl', mem := M } ∧
        R' 9 = BitVec.ofNat 64 0 ∧ R' 2 = BitVec.ofNat 64 remp ∧ R' 3 = BitVec.ofNat 64 (n - 1) ∧
        R' 0 = 18446744073709551615#64 ∧ R' 6 = BitVec.ofNat 64 (ulen + 1) ∧ R' 7 = (if s = 0 then 0#64 else 18446744073709551615#64) ∧
        R' 8 = 0 - BitVec.ofNat 64 s ∧ R' 1 = 0 - BitVec.ofNat 64 (64 - s) ∧ R' 4 = BitVec.ofNat 64 sf) := by
  have hcode := ku_lt
  have hnz : ¬ (BitVec.ofNat 64 remp) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hnz, e4, m_130, m_d0, m_e0, m_90, m_c0, m_c8, m_d8]
  refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp only [setRegF]; simp
    split <;> simp_all
  · simp only [setRegF]; simp
    bv_omega
  · simp only [setRegF]; simp
    bv_omega
  · simp [setRegF, e4]

set_option maxHeartbeats 8000000 in
theorem den_final_pos (s0 : State) (remp n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e2 : R 2 = BitVec.ofNat 64 remp) (e0 : R 0 = 18446744073709551615#64) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s))
    (e4 : R 4 = BitVec.ofNat 64 sf) (m_b8 : M.readLE (sf + 0xb8) 8 = n)
    (hsn : ¬ (18446744073709551616 - (64 - s)) % 64 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x394))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3db), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x394), flags := fl', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 sf ∧ (∀ k, k ∈ [5, 14] → R' k = R k) ∧
        M'.readLE (remp + 8 * (n - 1)) 8 = M.readLE (sf + 0x48 + 8 * (n - 1)) 8 / 2 ^ s ∧
        MemFrame M M' [(remp + 8 * (n - 1), remp + 8 * (n - 1) + 8)]) := by
  have hcode := ku_lt
  janus64_run [hsn, e2, e0, e1, e4, m_b8]
  have hu1 : M.readLE (sf + 0x48 + 8 * (n - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (sf + 0x48 + 8 * (n - 1)) 8; simpa using this
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF, e4]
  · intro k hk
    have : k ≠ 3 ∧ k ≠ 6 := by simp at hk; omega
    simp [setRegF, this.1, this.2]
  · rw [show remp + n * 8 - 8 = remp + 8 * (n - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show sf + n * 8 + 64 = sf + 0x48 + 8 * (n - 1) by omega]
    rw [show (18446744073709551616 - (64 - s)) % 64 = s by omega]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
    rw [Nat.mod_eq_of_lt (show M.readLE (sf + 0x48 + 8 * (n - 1)) 8 < 18446744073709551616 by simpa using hu1)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by simpa using hu1))
  · rw [show remp + n * 8 - 8 = remp + 8 * (n - 1) by omega]
    exact Janus.MemFrame.of_writeLE M _ (r := (remp + 8 * (n - 1), remp + 8 * (n - 1) + 8)) (List.Mem.head _) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem den_final_zero (s0 : State) (remp n ulen sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hn1 : 1 ≤ n) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e2 : R 2 = BitVec.ofNat 64 remp) (e0 : R 0 = 18446744073709551615#64) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - 0))
    (e4 : R 4 = BitVec.ofNat 64 sf) (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x394))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3db), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x394), flags := fl', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 sf ∧ (∀ k, k ∈ [5, 14] → R' k = R k) ∧
        M'.readLE (remp + 8 * (n - 1)) 8 = M.readLE (sf + 0x48 + 8 * (n - 1)) 8 / 2 ^ 0 ∧
        MemFrame M M' [(remp + 8 * (n - 1), remp + 8 * (n - 1) + 8)]) := by
  have hcode := ku_lt
  janus64_run [e2, e0, e1, e4, m_b8]
  have hu1 : M.readLE (sf + 0x48 + 8 * (n - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (sf + 0x48 + 8 * (n - 1)) 8; simpa using this
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF, e4]
  · intro k hk
    have : k ≠ 3 ∧ k ≠ 6 := by simp at hk; omega
    simp [setRegF, this.1, this.2]
  · rw [show remp + n * 8 - 8 = remp + 8 * (n - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show sf + n * 8 + 64 = sf + 0x48 + 8 * (n - 1) by omega]
    simp [Fv256.B.and_mask, Nat.mod_eq_of_lt hu1]
  · rw [show remp + n * 8 - 8 = remp + 8 * (n - 1) by omega]
    exact Janus.MemFrame.of_writeLE M _ (r := (remp + 8 * (n - 1), remp + 8 * (n - 1) + 8)) (List.Mem.head _) (by omega) (by omega)


set_option maxHeartbeats 8000000 in
theorem den_final (s0 : State) (remp n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hulen : n ≤ ulen) (hulen2 : ulen ≤ 4)
    (hrem : remp + 32 ≤ 2 ^ 48) (hra : M.accessible remp 32 true = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : remp + 32 ≤ sf ∨ sf + 0x140 ≤ remp)
    (e2 : R 2 = BitVec.ofNat 64 remp) (e0 : R 0 = 18446744073709551615#64) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s))
    (e4 : R 4 = BitVec.ofNat 64 sf) (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x394))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x3db), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x394), flags := fl', mem := M' } ∧
        R' 4 = BitVec.ofNat 64 sf ∧ (∀ k, k ∈ [5, 14] → R' k = R k) ∧
        M'.readLE (remp + 8 * (n - 1)) 8 = M.readLE (sf + 0x48 + 8 * (n - 1)) 8 / 2 ^ s ∧
        MemFrame M M' [(remp + 8 * (n - 1), remp + 8 * (n - 1) + 8)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact den_final_zero s0 remp n ulen sf R fl M hn hn1 hulen hulen2 hrem hra hsf hMs hsf0 hdisj e2 e0 e1 e4 m_b8
  · exact den_final_pos s0 remp n ulen s sf R fl M hs h hn hn1 hulen hulen2 hrem hra hsf hMs hsf0 hdisj e2 e0 e1 e4 m_b8 (by omega)

set_option maxHeartbeats 8000000 in
theorem epilogue (s0 : State) (sf rbpv ra : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hsf : sf + 0xf8 ≤ 2 ^ 48) (hsf0 : 8 ≤ sf) (hMs : M.accessible sf 0xf8 true = true)
    (e4 : R 4 = BitVec.ofNat 64 sf) (m_e8 : M.readLE (sf + 0xe8) 8 = rbpv) (m_f0 : M.readLE (sf + 0xf0) 8 = ra) (hra : ra < 2 ^ 47) :
    ReachesRet Extracted.program (BitVec.ofNat 64 ra)
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x394), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 ra, flags := fl', mem := M } ∧
        R' 4 = BitVec.ofNat 64 (sf + 0xf8) ∧ R' 5 = BitVec.ofNat 64 rbpv) := by
  have hcode := ku_lt
  have hra2 : M.readLE (sf + 0xf0) 8 < 2 ^ 47 := by rw [m_f0]; exact hra
  janus64_run [e4, m_e8, m_f0, hra2]
  refine ⟨_, _, rfl, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · simp [setRegF]

end Fv256.Amd64.UdivremF
