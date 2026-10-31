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

namespace Fv256.Amd64.UdivremD

set_option maxHeartbeats 8000000 in
theorem mid2_pos (s0 : State) (dp qp qcap ql up remp n ul ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = 4) (hulen : ulen ≤ 4) (hulen1 : n ≤ ulen)
    (hup : up + 32 ≤ 2 ^ 48) (hua : M.accessible up 32 false = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 32 ≤ sf ∨ sf + 0x140 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e12 : R 12 = BitVec.ofNat 64 ulen) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s)) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = 18446744073709551615#64)
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (ulen - 1) ∧ R' 1 = 0 - BitVec.ofNat 64 s ∧ R' 2 = BitVec.ofNat 64 (sf + 72) ∧
        R' 10 = BitVec.ofNat 64 (ulen + 1) ∧ R' 13 = 18446744073709551615#64 ∧
        (∀ k, k ∉ [0, 1, 2, 6, 10, 13] → R' k = R k) ∧
        M'.readLE (sf + 0xb8) 8 = n ∧
        (∀ j, j < 9 → j ≠ ulen → M'.readLE (sf + 0x48 + 8 * j) 8 = 0) ∧
        M'.readLE (sf + 0x48 + 8 * ulen) 8 = M.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0xb8, sf + 0xc0), (sf + 0x48, sf + 0x90)]) := by
  have hcode := ku_lt
  have hsn : ¬ (18446744073709551616 - s) % 64 = 0 := by omega
  have hu1 : M.readLE (up + 8 * (ulen - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * (ulen - 1)) 8; simpa using this
  janus64_run [hsn, e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, e2, e6]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (simp [setRegF]; bv_omega)
    | (simp [setRegF, hs1]; done)
    | (intro k hk
       have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 6 ∧ k ≠ 10 ∧ k ≠ 13 := by simpa using hk
       obtain ⟨k0, k1, k2, k6, k10, k13⟩ := hk'
       simp [setRegF, k0, k1, k2, k6, k10, k13])
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
       simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    | janus_frame
    | (intro j hj hne
       have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
       rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside] <;>
       simp)
    | (rw [show sf + 0x48 + 8 * ulen = sf + ulen * 8 + 72 by omega, Janus.Arm64.Memory.readLE_writeLE_self]
       rw [show up + ulen * 8 - 8 = up + 8 * (ulen - 1) by omega]
       have hm : ((if 63 - s + 1 < 64 then 18446744073709551615#64 else 0#64).toNat) = 2 ^ 64 - 1 := by simp [show 63 - s + 1 < 64 by omega]
       rw [hm, Nat.and_two_pow_sub_one_eq_mod]
       rw [show (18446744073709551616 - s) % 64 = 64 - s by omega]
       simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
       rw [Nat.mod_eq_of_lt (b := 18446744073709551616) hu1, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hu1)]
       exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hu1))
    | skip
  all_goals trace_state

set_option maxHeartbeats 8000000 in
theorem mid2_zero (s0 : State) (dp qp qcap ql up remp n ul ulen sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = 4) (hulen : ulen ≤ 4) (hulen1 : n ≤ ulen)
    (hup : up + 32 ≤ 2 ^ 48) (hua : M.accessible up 32 false = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 32 ≤ sf ∨ sf + 0x140 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e12 : R 12 = BitVec.ofNat 64 ulen) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - 0)) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - 0))
    (e8 : R 8 = 0 - BitVec.ofNat 64 0) (e13 : R 13 = BitVec.ofNat 64 (63 - 0)) (e15 : R 15 = 18446744073709551615#64)
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (ulen - 1) ∧ R' 1 = 0 - BitVec.ofNat 64 0 ∧ R' 2 = BitVec.ofNat 64 (sf + 72) ∧
        R' 10 = BitVec.ofNat 64 (ulen + 1) ∧ R' 13 = 0#64 ∧
        (∀ k, k ∉ [0, 1, 2, 6, 10, 13] → R' k = R k) ∧
        M'.readLE (sf + 0xb8) 8 = n ∧
        (∀ j, j < 9 → j ≠ ulen → M'.readLE (sf + 0x48 + 8 * j) 8 = 0) ∧
        M'.readLE (sf + 0x48 + 8 * ulen) 8 = M.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - 0) ∧
        MemFrame M M' [(sf + 0xb8, sf + 0xc0), (sf + 0x48, sf + 0x90)]) := by
  have hcode := ku_lt
  have hu1 : M.readLE (up + 8 * (ulen - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * (ulen - 1)) 8; simpa using this
  janus64_run [e12, e0, e1, e3, e7, e10, e11, e8, e13, e15, e9, e4, e2, e6]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (simp [setRegF]; bv_omega)
    | (intro k hk
       have hk' : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 6 ∧ k ≠ 10 ∧ k ≠ 13 := by simpa using hk
       obtain ⟨k0, k1, k2, k6, k10, k13⟩ := hk'
       simp [setRegF, k0, k1, k2, k6, k10, k13])
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
       simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    | janus_frame
    | (intro j hj hne
       have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
       rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside] <;>
       simp)
    | (rw [show sf + 0x48 + 8 * ulen = sf + ulen * 8 + 72 by omega, Janus.Arm64.Memory.readLE_writeLE_self]
       simp [Nat.div_eq_of_lt hu1, Nat.mod_one])
    | skip
  all_goals trace_state


set_option maxHeartbeats 8000000 in
theorem mid2 (s0 : State) (dp qp qcap ql up remp n ul ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = 4) (hulen : ulen ≤ 4) (hulen1 : n ≤ ulen)
    (hup : up + 32 ≤ 2 ^ 48) (hua : M.accessible up 32 false = true)
    (hsf : sf + 0x140 ≤ 2 ^ 48) (hMs : M.accessible sf 0x140 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 32 ≤ sf ∨ sf + 0x140 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e12 : R 12 = BitVec.ofNat 64 ulen) (e0 : R 0 = BitVec.ofNat 64 qp) (e1 : R 1 = 0 - BitVec.ofNat 64 (64 - s)) (e3 : R 3 = BitVec.ofNat 64 ql)
    (e7 : R 7 = BitVec.ofNat 64 up) (e10 : R 10 = BitVec.ofNat 64 remp) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = BitVec.ofNat 64 (63 - s)) (e15 : R 15 = 18446744073709551615#64)
    (e9 : R 9 = BitVec.ofNat 64 qcap) (e4 : R 4 = BitVec.ofNat 64 sf) (e2 : R 2 = BitVec.ofNat 64 n) (e6 : R 6 = BitVec.ofNat 64 ul) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x1a0), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (ulen - 1) ∧ R' 1 = 0 - BitVec.ofNat 64 s ∧ R' 2 = BitVec.ofNat 64 (sf + 72) ∧
        R' 10 = BitVec.ofNat 64 (ulen + 1) ∧ R' 13 = (if s = 0 then 0#64 else 18446744073709551615#64) ∧
        (∀ k, k ∉ [0, 1, 2, 6, 10, 13] → R' k = R k) ∧
        M'.readLE (sf + 0xb8) 8 = n ∧
        (∀ j, j < 9 → j ≠ ulen → M'.readLE (sf + 0x48 + 8 * j) 8 = 0) ∧
        M'.readLE (sf + 0x48 + 8 * ulen) 8 = M.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0xb8, sf + 0xc0), (sf + 0x48, sf + 0x90)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    refine Fv256.B.reachesRet_mono64 (mid2_zero s0 dp qp qcap ql up remp n ul ulen sf R fl M hn hn1 hul hulen hulen1 hup hua hsf hMs hsf0 hdisj hx15 e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6) ?_
    rintro S ⟨R', fl', M', hS, a0, a1, a2, a10, a13, hk, hm, hz, ht, hf⟩
    exact ⟨R', fl', M', hS, a0, a1, a2, a10, by simp [a13], hk, hm, hz, ht, hf⟩
  · refine Fv256.B.reachesRet_mono64 (mid2_pos s0 dp qp qcap ql up remp n ul ulen s sf R fl M hs h hn hn1 hul hulen hulen1 hup hua hsf hMs hsf0 hdisj hx15 e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6) ?_
    rintro S ⟨R', fl', M', hS, a0, a1, a2, a10, a13, hk, hm, hz, ht, hf⟩
    exact ⟨R', fl', M', hS, a0, a1, a2, a10, by simp [a13, Nat.pos_iff_ne_zero.mp h], hk, hm, hz, ht, hf⟩

end Fv256.Amd64.UdivremD
