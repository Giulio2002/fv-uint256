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


end Fv256.Amd64.UdivremF
