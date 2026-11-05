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
theorem mid2_pos {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = L) (hulen : ulen ≤ L) (hulen1 : n ≤ ulen)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
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
theorem mid2_zero {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul ulen sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = L) (hulen : ulen ≤ L) (hulen1 : n ≤ ulen)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
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
theorem mid2 {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (dp qp qcap ql up remp n ul ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hn : n ≤ 4) (hn1 : 1 ≤ n) (hul : ul = L) (hulen : ulen ≤ L) (hulen1 : n ≤ ulen)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
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
    refine Fv256.B.reachesRet_mono64 (mid2_zero hL s0 dp qp qcap ql up remp n ul ulen sf R fl M hn hn1 hul hulen hulen1 hup hua hsf hMs hsf0 hdisj hx15 e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6) ?_
    rintro S ⟨R', fl', M', hS, a0, a1, a2, a10, a13, hk, hm, hz, ht, hf⟩
    exact ⟨R', fl', M', hS, a0, a1, a2, a10, by simp [a13], hk, hm, hz, ht, hf⟩
  · refine Fv256.B.reachesRet_mono64 (mid2_pos hL s0 dp qp qcap ql up remp n ul ulen s sf R fl M hs h hn hn1 hul hulen hulen1 hup hua hsf hMs hsf0 hdisj hx15 e12 e0 e1 e3 e7 e10 e11 e8 e13 e15 e9 e4 e2 e6) ?_
    rintro S ⟨R', fl', M', hS, a0, a1, a2, a10, a13, hk, hm, hz, ht, hf⟩
    exact ⟨R', fl', M', hS, a0, a1, a2, a10, by simp [a13, Nat.pos_iff_ne_zero.mp h], hk, hm, hz, ht, hf⟩

set_option maxHeartbeats 8000000 in
theorem un_iter_pos {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up ulen s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hi : i + 1 < ulen) (hulen : ulen ≤ L)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up)
    (e0 : R 0 = BitVec.ofNat 64 (i + 1)) (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = 18446744073709551615#64) (e15 : R 15 = 18446744073709551615#64)
    (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e4 : R 4 = BitVec.ofNat 64 sf)
    (hsn1 : ¬ (18446744073709551616 - s) % 64 = 0) (hsn2 : ¬ (18446744073709551616 - (64 - s)) % 64 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x267), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x48 + 8 * (i + 1)) 8 = (M.readLE (up + 8 * (i + 1)) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (up + 8 * i) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0x48 + 8 * (i + 1), sf + 0x48 + 8 * (i + 1) + 8)]) := by
  have hcode := ku_lt
  have hmsb : (BitVec.ofNat 64 (i + 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hpos : ¬ (BitVec.ofNat 64 (i + 1)) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hsn1, hsn2, hmsb, hpos, e0, e7, e11, e8, e13, e15, e2, e4] until [ku + 0x267]
  have hdB : ∀ k, k < L → M.readLE (up + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * k) 8; simpa using this
  have hda1 := hdB (i + 1) (by omega)
  have hdb1 := hdB i (by omega)
  simp only [Nat.reducePow] at hda1 hdb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · intro k k0 k1 k6 k12
    simp [setRegF, k0, k1, k6, k12]
  · rw [show sf + (i + 1) * 8 + 72 = sf + 72 + 8 * (i + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show up + (i + 1) * 8 - 8 = up + 8 * i by omega, show up + (i + 1) * 8 = up + 8 * (i + 1) by omega]
    rw [Fv256.B.funnel_mach' _ _ s hs1 hs hda1 hdb1]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (Fv256.B.shl_carry_lt _ _ s (by omega) hdb1)
  · exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x48 + 8 * (i + 1), sf + 0x48 + 8 * (i + 1) + 8)) (List.Mem.head _) (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem un_iter_zero {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up ulen sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hi : i + 1 < ulen) (hulen : ulen ≤ L)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up)
    (e0 : R 0 = BitVec.ofNat 64 (i + 1)) (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - 0))
    (e8 : R 8 = 0 - BitVec.ofNat 64 0) (e13 : R 13 = 0#64) (e15 : R 15 = 18446744073709551615#64)
    (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e4 : R 4 = BitVec.ofNat 64 sf)
     :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x267), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x48 + 8 * (i + 1)) 8 = (M.readLE (up + 8 * (i + 1)) 8 * 2 ^ 0) % 2 ^ 64 + M.readLE (up + 8 * i) 8 / 2 ^ (64 - 0) ∧
        MemFrame M M' [(sf + 0x48 + 8 * (i + 1), sf + 0x48 + 8 * (i + 1) + 8)]) := by
  have hcode := ku_lt
  have hmsb : (BitVec.ofNat 64 (i + 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega
  have hpos : ¬ (BitVec.ofNat 64 (i + 1)) = 0#64 := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hmsb, hpos, e0, e7, e11, e8, e13, e15, e2, e4] until [ku + 0x267]
  have hdB : ∀ k, k < L → M.readLE (up + 8 * k) 8 < 2 ^ 64 := fun k _ => by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * k) 8; simpa using this
  have hda1 := hdB (i + 1) (by omega)
  have hdb1 := hdB i (by omega)
  simp only [Nat.reducePow] at hda1 hdb1
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]; bv_omega
  · intro k k0 k1 k6 k12
    simp [setRegF, k0, k1, k6, k12]
  · rw [show sf + (i + 1) * 8 + 72 = sf + 72 + 8 * (i + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [show up + (i + 1) * 8 - 8 = up + 8 * i by omega, show up + (i + 1) * 8 = up + 8 * (i + 1) by omega]
    simp [Fv256.B.and_mask, Nat.div_eq_of_lt hdb1, Nat.mod_eq_of_lt hda1, Nat.mod_one]
  · exact Janus.MemFrame.of_writeLE M _ (r := (sf + 0x48 + 8 * (i + 1), sf + 0x48 + 8 * (i + 1) + 8)) (List.Mem.head _) (by omega) (by omega)


set_option maxHeartbeats 8000000 in
theorem un_iter {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up ulen s sf i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hi : i + 1 < ulen) (hulen : ulen ≤ L)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up)
    (e0 : R 0 = BitVec.ofNat 64 (i + 1)) (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e8 : R 8 = 0 - BitVec.ofNat 64 s) (e13 : R 13 = (if s = 0 then 0#64 else 18446744073709551615#64)) (e15 : R 15 = 18446744073709551615#64)
    (e2 : R 2 = BitVec.ofNat 64 (sf + 72)) (e4 : R 4 = BitVec.ofNat 64 sf) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x267))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x267), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x267), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 i ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 12 → R' k = R k) ∧
        M'.readLE (sf + 0x48 + 8 * (i + 1)) 8 = (M.readLE (up + 8 * (i + 1)) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (up + 8 * i) 8 / 2 ^ (64 - s) ∧
        MemFrame M M' [(sf + 0x48 + 8 * (i + 1), sf + 0x48 + 8 * (i + 1) + 8)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact un_iter_zero hL s0 up ulen sf i R fl M hi hulen hup hua hsf hMs hsf0 hdisj e0 e7 e11 e8 (by simpa using e13) e15 e2 e4
  · have hne : s ≠ 0 := Nat.pos_iff_ne_zero.mp h
    exact un_iter_pos hL s0 up ulen s sf i R fl M hs h hi hulen hup hua hsf hMs hsf0 hdisj e0 e7 e11 e8 (by simpa [hne] using e13) e15 e2 e4 (by omega) (by omega)

set_option maxHeartbeats 8000000 in
theorem un_loop {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up ulen s sf : Nat) (hs : s ≤ 63) (hulen : ulen ≤ L)
    (hup : up + 8 * L ≤ 2 ^ 48) (hsf : sf + 0x138 ≤ 2 ^ 48) (hsf0 : 0x20 ≤ sf) (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) :
    ∀ i, i < ulen → ∀ (R : Nat → W64) (fl : Flags) (M : Memory), M.accessible up (8 * L) false = true → M.accessible sf 0x138 true = true →
      R 0 = BitVec.ofNat 64 i → R 7 = BitVec.ofNat 64 up → R 11 = 0 - BitVec.ofNat 64 (64 - s) → R 8 = 0 - BitVec.ofNat 64 s →
      R 13 = (if s = 0 then 0#64 else 18446744073709551615#64) → R 15 = 18446744073709551615#64 →
      R 2 = BitVec.ofNat 64 (sf + 72) → R 4 = BitVec.ofNat 64 sf →
      (∀ k, i < k → k < ulen → M.readLE (sf + 0x48 + 8 * k) 8 =
        (M.readLE (up + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (up + 8 * (k - 1)) 8 / 2 ^ (64 - s)) →
      ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x26c))
        { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x267), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl', mem := M' } ∧
          R' 0 = 0#64 ∧ (∀ k, k ≠ 0 → k ≠ 1 → k ≠ 6 → k ≠ 12 → R' k = R k) ∧
          (∀ k, 1 ≤ k → k < ulen → M'.readLE (sf + 0x48 + 8 * k) 8 =
            (M.readLE (up + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + M.readLE (up + 8 * (k - 1)) 8 / 2 ^ (64 - s)) ∧
          MemFrame M M' [(sf + 0x48 + 8, sf + 0x48 + 8 * (i + 1))]) := by
  intro i
  induction i with
  | zero =>
    intro hi R fl M hua hMs e0 e7 e11 e8 e13 e15 e2 e4 hinv
    have hcode := ku_lt
    have hz : R 0 = 0#64 := e0
    janus64_run [hz]
    refine ⟨_, _, M, rfl, by simp [hz], fun k _ _ _ _ => rfl, fun k hk1 hk2 => hinv k hk1 hk2, MemFrame.refl _ _⟩
  | succ i ih =>
    intro hi R fl M hua hMs e0 e7 e11 e8 e13 e15 e2 e4 hinv
    have h1 := un_iter hL s0 up ulen s sf i R fl M hs hi hulen hup hua hsf hMs hsf0 hdisj e0 e7 e11 e8 e13 e15 e2 e4
    refine Fv256.B.reachesRet_trans64 h1 ?_
    intro S1 hrip ⟨R1, fl1, M1, hS1, f0, fk, fmem, ffr⟩
    subst hS1
    have hdw : ∀ k, k < L → M1.readLE (up + 8 * k) 8 = M.readLE (up + 8 * k) 8 := fun k hk =>
      ffr.readLE _ _ (by simp [Outside]; omega)
    have hsl : ∀ a, (a + 8 ≤ sf + 0x48 + 8 * (i + 1) ∨ sf + 0x48 + 8 * (i + 1) + 8 ≤ a) → M1.readLE a 8 = M.readLE a 8 := fun a h =>
      ffr.readLE _ _ (by simp [Outside]; omega)
    have h2 := ih (by omega) R1 fl1 M1 (by rw [ffr.accessible]; exact hua) (by rw [ffr.accessible]; exact hMs) f0
      ((fk 7 (by omega) (by omega) (by omega) (by omega)).trans e7) ((fk 11 (by omega) (by omega) (by omega) (by omega)).trans e11)
      ((fk 8 (by omega) (by omega) (by omega) (by omega)).trans e8) ((fk 13 (by omega) (by omega) (by omega) (by omega)).trans e13)
      ((fk 15 (by omega) (by omega) (by omega) (by omega)).trans e15) ((fk 2 (by omega) (by omega) (by omega) (by omega)).trans e2)
      ((fk 4 (by omega) (by omega) (by omega) (by omega)).trans e4)
      (by
        intro k hk1 hk2
        rw [hdw k (by omega), hdw (k - 1) (by omega)]
        by_cases hk : k = i + 1
        · subst hk; exact fmem
        · rw [hsl _ (by omega)]; exact hinv k (by omega) hk2)
    refine Fv256.B.reachesRet_mono64 h2 ?_
    rintro S2 ⟨R2, fl2, M2, hS2, g0, gk, gmem, gfr⟩
    refine ⟨R2, fl2, M2, hS2, g0, fun k k0 k1 k6 k12 => (gk k k0 k1 k6 k12).trans (fk k k0 k1 k6 k12), fun k hk1 hk2 => ?_, ?_⟩
    · rw [gmem k hk1 hk2, hdw k (by omega), hdw (k - 1) (by omega)]
    · exact ffr.trans gfr (by intro a n' h; simp [Outside] at h ⊢; omega)

set_option maxHeartbeats 8000000 in
theorem midA_pos {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hulen : ulen ≤ L) (hn2 : 2 ≤ n) (hn : n ≤ 4)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n)
    (hsn : ¬ (18446744073709551616 - (64 - s)) % 64 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x29f))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x29f), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - s) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ s) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  have hcode := ku_lt
  have hn1 : ¬ n = 1 := by omega
  have hd0 : M.readLE up 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M up 8; simpa using this
  have hn1b : ¬ (BitVec.ofNat 64 n = 1#64) := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hsn, hn1, hn1b, e7, e11, e15, e4, m_b8]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 12 := by simpa using hk
       simp [setRegF, hk'.1, hk'.2])
    | janus_frame
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
       | (rw [show (18446744073709551616 - (64 - s)) % 64 = s by omega]; try simp only [Nat.reducePow]))
  all_goals trace_state

set_option maxHeartbeats 8000000 in
theorem midA_zero {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hulen : ulen ≤ L) (hn2 : 2 ≤ n) (hn : n ≤ 4)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - 0))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x29f))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x29f), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - 0) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ 0) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  have hcode := ku_lt
  have hn1 : ¬ n = 1 := by omega
  have hd0 : M.readLE up 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M up 8; simpa using this
  have hn1b : ¬ (BitVec.ofNat 64 n = 1#64) := by
    intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus64_run [hn1, hn1b, e7, e11, e15, e4, m_b8]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 12 := by simpa using hk
       simp [setRegF, hk'.1, hk'.2])
    | janus_frame
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
       | (simp [Nat.mod_eq_of_lt hd0]))
  all_goals trace_state


set_option maxHeartbeats 8000000 in
theorem midA {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hulen : ulen ≤ L) (hn2 : 2 ≤ n) (hn : n ≤ 4)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x29f))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x29f), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - s) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ s) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact midA_zero hL s0 up n ulen sf R fl M hulen hn2 hn hup hua hsf hMs hsf0 hdisj hx15 e7 e11 e15 e4 m_b8
  · exact midA_pos hL s0 up n ulen s sf R fl M hs h hulen hn2 hn hup hua hsf hMs hsf0 hdisj hx15 e7 e11 e15 e4 m_b8 (by omega)

set_option maxHeartbeats 8000000 in
theorem midA1_pos {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hs1 : 1 ≤ s) (hulen : ulen ≤ L) (hn1 : n = 1)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n)
    (hsn : ¬ (18446744073709551616 - (64 - s)) % 64 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x32e))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x32e), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - s) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ s) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  have hcode := ku_lt
  have hd0 : M.readLE up 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M up 8; simpa using this
  have hn1b : (BitVec.ofNat 64 n = 1#64) := by subst hn1; rfl
  janus64_run [hsn, hn1b, e7, e11, e15, e4, m_b8]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 12 := by simpa using hk
       simp [setRegF, hk'.1, hk'.2])
    | janus_frame
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
       | (rw [show (18446744073709551616 - (64 - s)) % 64 = s by omega]; try simp only [Nat.reducePow]))
  all_goals trace_state

set_option maxHeartbeats 8000000 in
theorem midA1_zero {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hulen : ulen ≤ L) (hn1 : n = 1)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - 0))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x32e))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x32e), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - 0) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ 0) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  have hcode := ku_lt
  have hd0 : M.readLE up 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M up 8; simpa using this
  have hn1b : (BitVec.ofNat 64 n = 1#64) := by subst hn1; rfl
  janus64_run [hn1b, e7, e11, e15, e4, m_b8]
  all_goals refine ⟨_, _, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (simp [setRegF]; done)
    | (intro k hk
       have hk' : k ≠ 1 ∧ k ≠ 12 := by simpa using hk
       simp [setRegF, hk'.1, hk'.2])
    | janus_frame
    | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self] <;>
       first
       | (simp only [Nat.reducePow]; done)
       | (simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
       | (simp [Nat.mod_eq_of_lt hd0]))
  all_goals trace_state


set_option maxHeartbeats 8000000 in
theorem midA1 {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) (s0 : State) (up n ulen s sf : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hs : s ≤ 63) (hulen : ulen ≤ L) (hn1 : n = 1)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hsf : sf + 0x138 ≤ 2 ^ 48) (hMs : M.accessible sf 0x138 true = true) (hsf0 : 0x20 ≤ sf)
    (hdisj : up + 8 * L ≤ sf ∨ sf + 0x138 ≤ up) (hx15 : s0.xmm 15 = 0)
    (e7 : R 7 = BitVec.ofNat 64 up) (e11 : R 11 = 0 - BitVec.ofNat 64 (64 - s))
    (e15 : R 15 = 18446744073709551615#64) (e4 : R 4 = BitVec.ofNat 64 sf)
    (m_b8 : M.readLE (sf + 0xb8) 8 = n) :
    ReachesRet Extracted.program (BitVec.ofNat 64 (ku + 0x32e))
      { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x26c), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x32e), flags := fl', mem := M' } ∧
        R' 12 = BitVec.ofNat 64 n ∧ (∀ k, k ∉ [1, 12] → R' k = R k) ∧
        M'.readLE (sf + 0xd8) 8 = 18446744073709551616 - (64 - s) ∧ M'.readLE (sf + 0xd0) 8 = 18446744073709551615 ∧
        M'.readLE (sf + 0x48) 8 = (M.readLE up 8 * 2 ^ s) % 2 ^ 64 ∧
        MemFrame M M' [(sf + 0xd0, sf + 0xe0), (sf + 0x48, sf + 0x50)]) := by
  rcases Nat.eq_zero_or_pos s with h | h
  · subst h
    exact midA1_zero hL s0 up n ulen sf R fl M hulen hn1 hup hua hsf hMs hsf0 hdisj hx15 e7 e11 e15 e4 m_b8
  · exact midA1_pos hL s0 up n ulen s sf R fl M hs h hulen hn1 hup hua hsf hMs hsf0 hdisj hx15 e7 e11 e15 e4 m_b8 (by omega)


end Fv256.Amd64.UdivremD
