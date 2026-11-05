import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB
import Fv256.Arm64.ShiftLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.UdivremA

abbrev ku : Nat := segAddr Extracted.program "github.com/holiman/uint256.udivrem"

abbrev dhead : Nat := ku + 0x30
abbrev dexit : Nat := ku + 0x4c
abbrev nhead : Nat := ku + 0xb4
abbrev nexit : Nat := ku + 0xbc

theorem ku_lt : ku + 0x440 < 2 ^ 47 := by decide

set_option maxHeartbeats 8000000 in
theorem dlen_loop (T : State) (ret : W64) (Q : State → Prop) (dp : Nat) (M : Memory) (R0 : Nat → W64)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (n : Nat), R' 9 = BitVec.ofNat 64 n → n ≤ 4 →
      (∀ j, n ≤ j → j < 4 → M.readLE (dp + 8 * j) 8 = 0) → (0 < n → M.readLE (dp + 8 * (n - 1)) 8 ≠ 0) →
      (∀ k, k ∉ [5, 9, 27] → R' k = R0 k) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 dexit, flags := fl', mem := M } Q) :
    ∀ t (R : Nat → W64) (fl : Flags), t ≤ 4 → R 6 = BitVec.ofNat 64 dp → R 5 = BitVec.ofNat 64 t - 1 →
      (∀ k, k ∉ [5, 9, 27] → R k = R0 k) →
      (∀ j, t ≤ j → j < 4 → M.readLE (dp + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 dhead, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : dhead
  janus_eval_nat hh2 : dexit
  simp only [hh2] at hK
  intro t
  induction t with
  | zero =>
    intro R fl ht r6 r5 hRu hz
    simp only [hh1]
    have hmsb : (BitVec.ofNat 64 0 - (1 : BitVec 64)).getLsbD 63 = true := by decide
    janus_run [r6, r5, hmsb] until [ku + 0x4c]
    refine hK _ _ 0 (by simp [setReg]) (by omega) (fun j _ _ => hz j (by omega) ‹_›) (fun h => absurd h (by omega)) ?_
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    rw [if_neg (by omega)]
    exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
  | succ t ih =>
    intro R fl ht r6 r5 hRu hz
    simp only [hh1]
    have hj : BitVec.ofNat 64 (t + 1) - (1 : BitVec 64) = BitVec.ofNat 64 t := by bv_omega
    rw [hj] at r5
    have hmsb : (BitVec.ofNat 64 t).getLsbD 63 = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow (by rw [BitVec.toNat_ofNat]; omega)
    have hdA : M.accessible (dp + t * 8) 8 false = true := Janus.Arm64.Memory.accessible_mono _ hda (by omega) (by omega)
    janus_run [r6, r5, hmsb] until [ku + 0x30, ku + 0x4c]
    · have hM : M.readLE (dp + t * 8) 8 = M.readLE (dp + 8 * t) 8 := by rw [Nat.mul_comm]
      refine ih _ fl (by omega) (by simp [setReg, r6]) (by simp [setReg]) ?_ ?_
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
        simp only [setReg]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
      · intro j hj1 hj2
        by_cases hjt : j = t
        · subst hjt; rw [← hM]; exact hbr
        · exact hz j (by omega) hj2
    · have hM : M.readLE (dp + t * 8) 8 = M.readLE (dp + 8 * t) 8 := by rw [Nat.mul_comm]
      refine hK _ _ (t + 1) ?_ ht (fun j h1 h2 => hz j h1 h2) (fun _ => by rw [show t + 1 - 1 = t by omega, ← hM]; exact hbr) ?_
      · simp only [setReg]; simp; bv_omega
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
        simp only [setReg]
        rw [if_neg (by omega), if_neg (by omega)]
        exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)


set_option maxHeartbeats 8000000 in
theorem pro1 (s : State) (ret : W64) (Q : State → Prop)
    (hpc : s.pc = BitVec.ofNat 64 ku)
    (hgd : GuardOK s 96) (hst : StackOK s 232 72)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), R' 5 = 3#64 → R' 29 = s.sp - 232#64 → (∀ k, k ∉ [5, 16, 17, 29] → R' k = s.regs k) →
      MemFrame s.mem M' [(s.sp.toNat - 232, s.sp.toNat - 216), (s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat + 32, s.sp.toNat + 40)] →
      M'.readLE (s.sp.toNat - 224) 8 = (s.regs 30).toNat → M'.readLE (s.sp.toNat - 232) 8 = (s.regs 29).toNat →
      M'.readLE (s.sp.toNat + 8) 8 = (s.regs 0).toNat → M'.readLE (s.sp.toNat + 32) 8 = (s.regs 3).toNat →
      ReachesRet Extracted.program ret { s with regs := R', sp := s.sp - 224#64, pc := BitVec.ofNat 64 dhead, flags := fl', mem := M' } Q) :
    ReachesRet Extracted.program ret s Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : dhead
  simp only [hh1] at hK
  obtain ⟨hg1, hg2, hg3⟩ := hgd
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_run until [ku + 0x30]
  refine hK _ _ _ (by simp [setReg]) (by simp [setReg]) ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · have h0 := MemFrame.of_writeLE s.mem (k := 8) (BitVec.toNat (s.regs 30)) (rs := [(s.sp.toNat - 232, s.sp.toNat - 216), (s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat + 32, s.sp.toNat + 40)]) (a := s.sp.toNat - 224) (r := (s.sp.toNat - 232, s.sp.toNat - 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h1 := h0.writeLE (a := s.sp.toNat - 232) (k := 8) (BitVec.toNat (s.regs 29)) (r := (s.sp.toNat - 232, s.sp.toNat - 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h2 := h1.writeLE (a := s.sp.toNat + 8) (k := 8) (BitVec.toNat (s.regs 0)) (r := (s.sp.toNat + 8, s.sp.toNat + 16)) (by simp) (by simp <;> omega) (by simp <;> omega)
    exact h2.writeLE (a := s.sp.toNat + 32) (k := 8) (BitVec.toNat (s.regs 3)) (r := (s.sp.toNat + 32, s.sp.toNat + 40)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 30).isLt
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 29).isLt
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 0).isLt
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 3).isLt


set_option maxHeartbeats 8000000 in
theorem pro2 (T : State) (ret : W64) (Q : State → Prop) (dp n : Nat) (M : Memory) (R : Nat → W64) (fl : Flags)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (r9 : R 9 = BitVec.ofNat 64 n) (r6 : R 6 = BitVec.ofNat 64 dp)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true)
    (hdtop : M.readLE (dp + 8 * (n - 1)) 8 ≠ 0)
    (hsp : 0x138 ≤ T.sp.toNat) (hspb : T.sp.toNat + 0x138 ≤ 2 ^ 48) (hal : T.sp.toNat % 16 = 0)
    (hMs : M.accessible T.sp.toNat 0x138 true = true)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory) (s : Nat), s ≤ 63 → s = clzNat 64 (M.readLE (dp + 8 * (n - 1)) 8) →
      R' 10 = BitVec.ofNat 64 (n - 1) → R' 5 = BitVec.ofNat 64 (n - 1) → R' 9 = BitVec.ofNat 64 n →
      R' 11 = BitVec.ofNat 64 s → R' 12 = BitVec.ofNat 64 (T.sp.toNat + 160) → R' 13 = BitVec.ofNat 64 (s + 64) →
      (∀ k, k ∉ [5, 10, 11, 12, 13, 27] → R' k = R k) →
      MemFrame M M' [(T.sp.toNat + 160, T.sp.toNat + 192)] → (∀ j, j < 4 → M'.readLE (T.sp.toNat + 160 + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 nhead, flags := fl', mem := M' } Q) :
    ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 dexit, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : nhead
  janus_eval_nat hh2 : dexit
  simp only [hh1] at hK
  simp only [hh2]
  have hdA : M.accessible (dp + 8 * (n - 1)) 8 false = true := Janus.Arm64.Memory.accessible_mono _ hda (by omega) (by omega)
  have hdn : M.readLE (dp + (n - 1) * 8) 8 = M.readLE (dp + 8 * (n - 1)) 8 := by rw [Nat.mul_comm]
  janus_run [r9, r6, hdn] until [ku + 0xb4]
  have hdtB : M.readLE (dp + 8 * (n - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (dp + 8 * (n - 1)) 8; simpa using this
  obtain ⟨hs63, _, _⟩ := Fv256.B.clz_norm _ hdtop hdtB
  refine hK _ _ _ _ hs63 rfl (by simp [setReg]; bv_omega) (by simp [setReg]; bv_omega) (by simp [setReg, r9]) (by simp [setReg])
    (by simp only [setReg]; simp only [show (12 : Nat) ≠ 27 by decide, show (12 : Nat) ≠ 13 by decide, if_false, if_true, ite_true, ite_false]
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    (by simp [setReg]; bv_omega) ?_ ?_ ?_
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · have h0 := MemFrame.of_writeLE M (k := 8) 0 (rs := [(T.sp.toNat + 160, T.sp.toNat + 192)]) (a := T.sp.toNat + 160) (r := (T.sp.toNat + 160, T.sp.toNat + 192)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h1 := h0.writeLE (a := T.sp.toNat + 168) (k := 8) 0 (r := (T.sp.toNat + 160, T.sp.toNat + 192)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h2 := h1.writeLE (a := T.sp.toNat + 176) (k := 8) 0 (r := (T.sp.toNat + 160, T.sp.toNat + 192)) (by simp) (by simp <;> omega) (by simp <;> omega)
    exact h2.writeLE (a := T.sp.toNat + 184) (k := 8) 0 (r := (T.sp.toNat + 160, T.sp.toNat + 192)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]


set_option maxHeartbeats 8000000 in
theorem dn_loop (T : State) (ret : W64) (Q : State → Prop) (dp n s : Nat) (M0 : Memory) (R0 : Nat → W64)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (hs : s ≤ 63)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M0.accessible dp 32 false = true)
    (hdisj : dp + 32 ≤ T.sp.toNat + 160 ∨ T.sp.toNat + 192 ≤ dp) (hMa0 : M0.accessible (T.sp.toNat + 160) 32 true = true)
    (hsp : 0x138 ≤ T.sp.toNat) (hspb : T.sp.toNat + 0x138 ≤ 2 ^ 48)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
      R' 10 = 0#64 → (∀ k, k ∉ [10, 14, 15, 16, 17] → R' k = R0 k) →
      MemFrame M0 M' [(T.sp.toNat + 160, T.sp.toNat + 192)] →
      (∀ j, 1 ≤ j → j < n → M'.readLE (T.sp.toNat + 160 + 8 * j) 8 = (M0.readLE (dp + 8 * j) 8 * 2 ^ s) % 2 ^ 64 + M0.readLE (dp + 8 * (j - 1)) 8 / 2 ^ (64 - s)) →
      (∀ j, n ≤ j → j < 4 → M'.readLE (T.sp.toNat + 160 + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 nexit, flags := fl', mem := M' } Q) :
    ∀ t (R : Nat → W64) (fl : Flags) (M : Memory), t ≤ n - 1 →
      R 6 = BitVec.ofNat 64 dp → R 10 = BitVec.ofNat 64 t → R 11 = BitVec.ofNat 64 s → R 13 = BitVec.ofNat 64 (s + 64) →
      R 12 = BitVec.ofNat 64 (T.sp.toNat + 160) → (∀ k, k ∉ [10, 14, 15, 16, 17] → R k = R0 k) →
      MemFrame M0 M [(T.sp.toNat + 160, T.sp.toNat + 192)] →
      (∀ j, t < j → j < n → M.readLE (T.sp.toNat + 160 + 8 * j) 8 = (M0.readLE (dp + 8 * j) 8 * 2 ^ s) % 2 ^ 64 + M0.readLE (dp + 8 * (j - 1)) 8 / 2 ^ (64 - s)) →
      (∀ j, n ≤ j → j < 4 → M.readLE (T.sp.toNat + 160 + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 nhead, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : nhead
  janus_eval_nat hh2 : nexit
  simp only [hh2] at hK
  intro t
  induction t with
  | zero =>
    intro R fl M ht r6 r10 r11 r13 r12 hRu hfr hdn hz
    simp only [hh1]
    have hMa : M.accessible (T.sp.toNat + 160) 32 true = true := by rw [hfr.accessible]; exact hMa0
    have hMd : M.accessible dp 32 false = true := by rw [hfr.accessible]; exact hda
    janus_run [r10] until [ku + 0xbc]
    refine hK _ _ _ r10 hRu hfr (fun j h1 h2 => hdn j (by omega) h2) hz
  | succ t ih =>
    intro R fl M ht r6 r10 r11 r13 r12 hRu hfr hdn hz
    simp only [hh1]
    have hMa : M.accessible (T.sp.toNat + 160) 32 true = true := by rw [hfr.accessible]; exact hMa0
    have hMd : M.accessible dp 32 false = true := by rw [hfr.accessible]; exact hda
    janus_run [r10, r6, r11, r13, r12] until [ku + 0xb4]
    have hd1 := Janus.Arm64.Memory.readLE_lt M0 (dp + (t + 1) * 8) 8
    have hd0 := Janus.Arm64.Memory.readLE_lt M0 (dp + 8 * t) 8
    simp only [Nat.reducePow] at hd1 hd0
    have hval := Fv256.Arm64.Shift.dn_val (M0.readLE (dp + (t + 1) * 8) 8) (M0.readLE (dp + 8 * t) 8) s hs hd1 hd0
    refine ih _ _ _ (by omega) (by simp [setReg, r6]) ?_ (by simp [setReg, r11]) (by simp [setReg, r13]) (by simp [setReg, r12]) ?_ ?_ ?_ ?_
    · simp only [setReg]; simp; bv_omega
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp only [setReg]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    · exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
    · intro j hj1 hj2
      by_cases hjt : j = t + 1
      · subst hjt
        rw [show T.sp.toNat + 160 + (t + 1) * 8 = T.sp.toNat + 160 + 8 * (t + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
        have hd1' : M0.readLE (dp + 8 * (t + 1)) 8 = M0.readLE (dp + (t + 1) * 8) 8 := by rw [Nat.mul_comm]
        rw [show t + 1 - 1 = t by omega, hd1', hval]
        simp only [Nat.reducePow]
        exact Nat.mod_eq_of_lt (Fv256.B.shl_carry_lt _ _ s (by omega) hd0)
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hdn j (by omega) hj2
    · intro j hj1 hj2
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hz j hj1 hj2

end Fv256.Arm64.UdivremA
