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
abbrev uhead : Nat := ku + 0xe0
abbrev uexit : Nat := ku + 0xf8
abbrev ltpc : Nat := ku + 0x158
abbrev lhead : Nat := ku + 0x1bc
abbrev lexit : Nat := ku + 0x1c4
abbrev by1pc : Nat := ku + 0x230
abbrev by1ret : Nat := ku + 0x244
abbrev rhead : Nat := ku + 0x2a0
abbrev rexit : Nat := ku + 0x2c4
abbrev knret : Nat := ku + 0x210
abbrev knpc : Nat := ku + 0x20c

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
    (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48) (hal : T.sp.toNat % 16 = 0)
    (hMs : M.accessible T.sp.toNat 296 true = true)
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
    (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
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

set_option maxHeartbeats 8000000 in
theorem ulen_loop (T : State) (ret : W64) (Q : State → Prop) (up L : Nat) (M : Memory) (R0 : Nat → W64)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (n : Nat), R' 10 = BitVec.ofNat 64 n → n ≤ L →
      (∀ j, n ≤ j → j < L → M.readLE (up + 8 * j) 8 = 0) → (0 < n → M.readLE (up + 8 * (n - 1)) 8 ≠ 0) →
      (∀ k, k ∉ [10, 14] → R' k = R0 k) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 uexit, flags := fl', mem := M } Q) :
    ∀ t (R : Nat → W64) (fl : Flags), t ≤ L → R 3 = BitVec.ofNat 64 up → R 14 = BitVec.ofNat 64 t - 1 →
      (∀ k, k ∉ [10, 14] → R k = R0 k) →
      (∀ j, t ≤ j → j < L → M.readLE (up + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 uhead, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : uhead
  janus_eval_nat hh2 : uexit
  simp only [hh2] at hK
  intro t
  induction t with
  | zero =>
    intro R fl ht r3 r14 hRu hz
    simp only [hh1]
    have hmsb : (BitVec.ofNat 64 0 - (1 : BitVec 64)).getLsbD 63 = true := by decide
    janus_run [r3, r14, hmsb] until [ku + 0xf8]
    refine hK _ _ 0 (by simp [setReg]) (by omega) (fun j _ _ => hz j (by omega) ‹_›) (fun h => absurd h (by omega)) ?_
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
    exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
  | succ t ih =>
    intro R fl ht r3 r14 hRu hz
    simp only [hh1]
    have hj : BitVec.ofNat 64 (t + 1) - (1 : BitVec 64) = BitVec.ofNat 64 t := by bv_omega
    rw [hj] at r14
    have hmsb : (BitVec.ofNat 64 t).getLsbD 63 = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow (by rw [BitVec.toNat_ofNat]; omega)
    have hdA : M.accessible (up + t * 8) 8 false = true := Janus.Arm64.Memory.accessible_mono _ hua (by omega) (by omega)
    janus_run [r3, r14, hmsb] until [ku + 0xe0, ku + 0xf8]
    · have hM : M.readLE (up + t * 8) 8 = M.readLE (up + 8 * t) 8 := by rw [Nat.mul_comm]
      refine ih _ fl (by omega) (by simp [setReg, r3]) (by simp [setReg]) ?_ ?_
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
        simp only [setReg]
        repeat' rw [if_neg (by omega)]
        exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
      · intro j hj1 hj2
        by_cases hjt : j = t
        · subst hjt; rw [← hM]; exact hbr
        · exact hz j (by omega) hj2
    · have hM : M.readLE (up + t * 8) 8 = M.readLE (up + 8 * t) 8 := by rw [Nat.mul_comm]
      refine hK _ _ (t + 1) ?_ ht (fun j h1 h2 => hz j h1 h2) (fun _ => by rw [show t + 1 - 1 = t by omega, ← hM]; exact hbr) ?_
      · simp only [setReg]; simp; bv_omega
      · intro k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
        simp only [setReg]
        repeat' rw [if_neg (by omega)]
        exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)




set_option maxHeartbeats 8000000 in
theorem pro3 (T : State) (ret : W64) (Q : State → Prop) (dp n s L : Nat) (M0 M : Memory) (R : Nat → W64) (fl : Flags)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (hs : s ≤ 63) (hL : 1 ≤ L) (hL8 : L ≤ 8)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M0.accessible dp 32 false = true)
    (hMa0 : M0.accessible (T.sp.toNat + 160) 32 true = true)
    (hfr : MemFrame M0 M [(T.sp.toNat + 160, T.sp.toNat + 192)])
    (hdisj : dp + 32 ≤ T.sp.toNat + 160 ∨ T.sp.toNat + 192 ≤ dp)
    (r6 : R 6 = BitVec.ofNat 64 dp) (r9 : R 9 = BitVec.ofNat 64 n) (r11 : R 11 = BitVec.ofNat 64 s)
    (r4 : R 4 = BitVec.ofNat 64 L)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), R' 14 = BitVec.ofNat 64 L - 1 →
      (∀ k, k ∉ [10, 14] → R' k = R k) →
      MemFrame M0 M' [(T.sp.toNat + 160, T.sp.toNat + 192)] →
      M'.readLE (T.sp.toNat + 160) 8 = (M0.readLE dp 8 * 2 ^ s) % 2 ^ 64 →
      (∀ j, 1 ≤ j → M'.readLE (T.sp.toNat + 160 + 8 * j) 8 = M.readLE (T.sp.toNat + 160 + 8 * j) 8) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 uhead, flags := fl', mem := M' } Q) :
    ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 nexit, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : uhead
  janus_eval_nat hh2 : nexit
  simp only [hh1] at hK
  simp only [hh2]
  have hMa : M.accessible (T.sp.toNat + 160) 32 true = true := by rw [hfr.accessible]; exact hMa0
  have hMd : M.accessible dp 32 false = true := by rw [hfr.accessible]; exact hda
  have hd0 : M.readLE dp 8 = M0.readLE dp 8 := hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hR9 : ¬ (R 9 = 0#64) := by
    rw [r9]; intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  janus_run [r6, r9, r11, r4, hd0, hR9] until [ku + 0xe0]
  have hv : (if s < 64 then BitVec.ofNat 64 (M0.readLE dp 8 * 2 ^ (s % 64)) else 0#64).toNat = (M0.readLE dp 8 * 2 ^ s) % 2 ^ 64 := by
    have hs64 : s % 64 = s := Nat.mod_eq_of_lt (by omega)
    rw [if_pos (by omega), BitVec.toNat_ofNat, hs64]
  refine hK _ _ _ (by simp [setReg]) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
  · exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
  · rw [Janus.Arm64.Memory.readLE_writeLE_self, hv]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
  · intro j hj
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]


set_option maxHeartbeats 8000000 in
theorem un_loop (T : State) (ret : W64) (Q : State → Prop) (up ulen s : Nat) (M0 : Memory) (R0 : Nat → W64)
    (hu1 : 1 ≤ ulen) (hul : ulen ≤ 8) (hs : s ≤ 63)
    (hup : up + 8 * ulen ≤ 2 ^ 48) (hua : M0.accessible up (8 * ulen) false = true)
    (hdisj : up + 8 * ulen ≤ T.sp.toNat + 80 ∨ T.sp.toNat + 152 ≤ up) (hMa0 : M0.accessible (T.sp.toNat + 80) 72 true = true)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
      R' 16 = 0#64 → (∀ k, k ∉ [10, 16, 17, 19] → R' k = R0 k) →
      MemFrame M0 M' [(T.sp.toNat + 80, T.sp.toNat + 152)] →
      (∀ j, 1 ≤ j → j < ulen → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = (M0.readLE (up + 8 * j) 8 * 2 ^ s) % 2 ^ 64 + M0.readLE (up + 8 * (j - 1)) 8 / 2 ^ (64 - s)) →
      (∀ j, ulen ≤ j → j < 9 → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = M0.readLE (T.sp.toNat + 80 + 8 * j) 8) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 lexit, flags := fl', mem := M' } Q) :
    ∀ t (R : Nat → W64) (fl : Flags) (M : Memory), t ≤ ulen - 1 →
      R 3 = BitVec.ofNat 64 up → R 16 = BitVec.ofNat 64 t → R 11 = BitVec.ofNat 64 s → R 13 = BitVec.ofNat 64 (64 - s) →
      R 14 = BitVec.ofNat 64 (T.sp.toNat + 80) → (∀ k, k ∉ [10, 16, 17, 19] → R k = R0 k) →
      MemFrame M0 M [(T.sp.toNat + 80, T.sp.toNat + 152)] →
      (∀ j, t < j → j < ulen → M.readLE (T.sp.toNat + 80 + 8 * j) 8 = (M0.readLE (up + 8 * j) 8 * 2 ^ s) % 2 ^ 64 + M0.readLE (up + 8 * (j - 1)) 8 / 2 ^ (64 - s)) →
      (∀ j, ulen ≤ j → j < 9 → M.readLE (T.sp.toNat + 80 + 8 * j) 8 = M0.readLE (T.sp.toNat + 80 + 8 * j) 8) →
      ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 lhead, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : lhead
  janus_eval_nat hh2 : lexit
  simp only [hh2] at hK
  intro t
  induction t with
  | zero =>
    intro R fl M ht r3 r16 r11 r13 r14 hRu hfr hdn hz
    simp only [hh1]
    janus_run [r16] until [ku + 0x1c4]
    exact hK _ _ _ r16 hRu hfr (fun j h1 h2 => hdn j (by omega) h2) hz
  | succ t ih =>
    intro R fl M ht r3 r16 r11 r13 r14 hRu hfr hdn hz
    simp only [hh1]
    have hMa : M.accessible (T.sp.toNat + 80) 72 true = true := by rw [hfr.accessible]; exact hMa0
    have hMu : M.accessible up (8 * ulen) false = true := by rw [hfr.accessible]; exact hua
    janus_run [r16, r3, r11, r13, r14] until [ku + 0x1bc]
    have hd1 := Janus.Arm64.Memory.readLE_lt M0 (up + (t + 1) * 8) 8
    have hd0 := Janus.Arm64.Memory.readLE_lt M0 (up + 8 * t) 8
    simp only [Nat.reducePow] at hd1 hd0
    have hval := Fv256.Arm64.Shift.un_val (M0.readLE (up + (t + 1) * 8) 8) (M0.readLE (up + 8 * t) 8) s hs hd1 hd0
    refine ih _ _ _ (by omega) (by simp [setReg, r3]) ?_ (by simp [setReg, r11]) (by simp [setReg, r13]) (by simp [setReg, r14]) ?_ ?_ ?_ ?_
    · simp only [setReg]; simp; bv_omega
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp only [setReg]
      repeat' rw [if_neg (by omega)]
      exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    · exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
    · intro j hj1 hj2
      by_cases hjt : j = t + 1
      · subst hjt
        rw [show T.sp.toNat + 80 + (t + 1) * 8 = T.sp.toNat + 80 + 8 * (t + 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self]
        have hd1' : M0.readLE (up + 8 * (t + 1)) 8 = M0.readLE (up + (t + 1) * 8) 8 := by rw [Nat.mul_comm]
        rw [show t + 1 - 1 = t by omega, hd1', hval]
        simp only [Nat.reducePow]
        exact Nat.mod_eq_of_lt (Fv256.B.shl_carry_lt _ _ s (by omega) hd0)
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hdn j (by omega) hj2
    · intro j hj1 hj2
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hz j hj1 hj2


set_option maxHeartbeats 8000000 in
theorem pro4 (T : State) (ret : W64) (Q : State → Prop) (up n ulen s L : Nat) (M : Memory) (R : Nat → W64) (fl : Flags)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (hs : s ≤ 63) (hL8 : L ≤ 8) (hu1 : 1 ≤ ulen) (hul : ulen ≤ L)
    (hup : up + 8 * L ≤ 2 ^ 48) (hua : M.accessible up (8 * L) false = true)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hMa : M.accessible T.sp.toNat 296 true = true)
    (hdisj : up + 8 * L ≤ T.sp.toNat ∨ T.sp.toNat + 296 ≤ up)
    (r3 : R 3 = BitVec.ofNat 64 up) (r4 : R 4 = BitVec.ofNat 64 L) (r9 : R 9 = BitVec.ofNat 64 n) (r10 : R 10 = BitVec.ofNat 64 ulen)
    (r11 : R 11 = BitVec.ofNat 64 s) (r13 : R 13 = BitVec.ofNat 64 (s + 64))
    (hge : n ≤ ulen)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), R' 14 = BitVec.ofNat 64 (T.sp.toNat + 80) → R' 15 = BitVec.ofNat 64 (ulen + 1) →
      R' 16 = BitVec.ofNat 64 (ulen - 1) → R' 13 = BitVec.ofNat 64 (64 - s) → (∀ k, k ∉ [13, 14, 15, 16, 17, 19] → R' k = R k) →
      MemFrame M M' [(T.sp.toNat + 80, T.sp.toNat + 152)] →
      M'.readLE (T.sp.toNat + 80 + 8 * ulen) 8 = M.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - s) →
      (∀ j, j < ulen → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = 0) → (∀ j, ulen < j → j < 9 → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = 0) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 lhead, flags := fl', mem := M' } Q) :
    ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 uexit, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : uexit
  janus_eval_nat hh2 : lhead
  simp only [hh2] at hK
  simp only [hh1]
  have hA : ¬ (ulen < n) := by omega
  have hup1 : M.readLE (up + (ulen - 1) * 8) 8 = M.readLE (up + 8 * (ulen - 1)) 8 := by rw [Nat.mul_comm]
  janus_run [r3, r4, r9, r10, r11, r13, hup1] until [ku + 0x1bc]
  have hyB : M.readLE (up + 8 * (ulen - 1)) 8 < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt M (up + 8 * (ulen - 1)) 8; simpa using this
  have hsh := Fv256.Arm64.Shift.shr_val _ s hs hyB
  refine hK _ _ _ (by simp only [setReg]; simp; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add])
    (by simp [setReg]; bv_omega) (by simp [setReg]; bv_omega) (by simp only [setReg]; simp; bv_omega) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
  · have h0 := MemFrame.of_writeLE M (k := 8) 0 (rs := [(T.sp.toNat + 80, T.sp.toNat + 152)]) (a := T.sp.toNat + 80) (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h1 := h0.writeLE (a := T.sp.toNat + 88) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h2 := h1.writeLE (a := T.sp.toNat + 96) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h3 := h2.writeLE (a := T.sp.toNat + 104) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h4 := h3.writeLE (a := T.sp.toNat + 112) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h5 := h4.writeLE (a := T.sp.toNat + 120) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h6 := h5.writeLE (a := T.sp.toNat + 128) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h7 := h6.writeLE (a := T.sp.toNat + 136) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    have h8 := h7.writeLE (a := T.sp.toNat + 144) (k := 8) 0 (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
    exact h8.writeLE (a := T.sp.toNat + (80 + ulen * 8)) (k := 8) _ (r := (T.sp.toNat + 80, T.sp.toNat + 152)) (by simp) (by simp <;> omega) (by simp <;> omega)
  · rw [show T.sp.toNat + 80 + 8 * ulen = T.sp.toNat + (80 + ulen * 8) by omega, Janus.Arm64.Memory.readLE_writeLE_self, hsh]
    simp only [Nat.reducePow]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hyB)
  · intro j hj
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (exfalso; omega) | simp (disch := omega) only [Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · intro j hj1 hj2
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (exfalso; omega) | simp (disch := omega) only [Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd, Nat.add_zero, Nat.mul_zero, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]


set_option maxHeartbeats 8000000 in
theorem pro5 (T : State) (ret : W64) (Q : State → Prop) (up n ulen s L remp : Nat) (M0 M : Memory) (R : Nat → W64) (fl : Flags)
    (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (hs : s ≤ 63) (hremp : remp < 2 ^ 64) (hul : ulen ≤ 8) (hu1 : 1 ≤ ulen)
    (hup : up + 8 * ulen ≤ 2 ^ 48) (hua : M0.accessible up (8 * ulen) false = true)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hMa : M0.accessible T.sp.toNat 296 true = true)
    (hfr : MemFrame M0 M [(T.sp.toNat + 80, T.sp.toNat + 152)])
    (hus : up + 8 * ulen ≤ T.sp.toNat ∨ T.sp.toNat + 296 ≤ up)
    (r3 : R 3 = BitVec.ofNat 64 up) (r7 : R 7 = BitVec.ofNat 64 remp) (r9 : R 9 = BitVec.ofNat 64 n)
    (r11 : R 11 = BitVec.ofNat 64 s) (r5 : R 5 = BitVec.ofNat 64 (n - 1)) (r13 : R 13 = BitVec.ofNat 64 (64 - s))
    (r15 : R 15 = BitVec.ofNat 64 (ulen + 1)) (r12 : R 12 = BitVec.ofNat 64 (T.sp.toNat + 160))
    (r14 : R 14 = BitVec.ofNat 64 (T.sp.toNat + 80))
    (hK1 : n = 1 → ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), (∀ k, k ≠ 10 → R' k = R k) →
      MemFrame M M' [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)] →
      M'.readLE (T.sp.toNat + 80) 8 = (M0.readLE up 8 * 2 ^ s) % 2 ^ 64 →
      (∀ j, 1 ≤ j → j < 9 → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = M.readLE (T.sp.toNat + 80 + 8 * j) 8) →
      M'.readLE (T.sp.toNat + 288) 8 = remp → M'.readLE (T.sp.toNat + 208) 8 = s →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 by1pc, flags := fl', mem := M' } Q)
    (hK2 : n ≠ 1 → ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), R' 3 = BitVec.ofNat 64 (T.sp.toNat + 80) → R' 4 = BitVec.ofNat 64 (ulen + 1) →
      R' 5 = 9#64 → R' 6 = BitVec.ofNat 64 (T.sp.toNat + 160) → R' 7 = BitVec.ofNat 64 n → R' 8 = 4#64 →
      (∀ k, k ∉ [3, 4, 5, 6, 7, 8, 10] → R' k = R k) →
      MemFrame M M' [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)] →
      M'.readLE (T.sp.toNat + 80) 8 = (M0.readLE up 8 * 2 ^ s) % 2 ^ 64 →
      (∀ j, 1 ≤ j → j < 9 → M'.readLE (T.sp.toNat + 80 + 8 * j) 8 = M.readLE (T.sp.toNat + 80 + 8 * j) 8) →
      M'.readLE (T.sp.toNat + 288) 8 = remp → M'.readLE (T.sp.toNat + 208) 8 = s →
      M'.readLE (T.sp.toNat + 200) 8 = n - 1 → M'.readLE (T.sp.toNat + 152) 8 = ulen + 1 → M'.readLE (T.sp.toNat + 192) 8 = 64 - s →
      (∀ j, j < 4 → M'.readLE (T.sp.toNat + 160 + 8 * j) 8 = M.readLE (T.sp.toNat + 160 + 8 * j) 8) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 knpc, flags := fl', mem := M' } Q) :
    ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 lexit, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : lexit
  janus_eval_nat hh2 : by1pc
  janus_eval_nat hh3 : knpc
  simp only [hh2, hh3] at hK1 hK2
  simp only [hh1]
  have hu0 : M.readLE up 8 = M0.readLE up 8 := hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hMu : M.accessible up (8 * ulen) false = true := by rw [hfr.accessible]; exact hua
  have hMs : M.accessible T.sp.toNat 296 true = true := by rw [hfr.accessible]; exact hMa
  have hu0' : ((M.writeLE (T.sp.toNat + 288) 8 remp).writeLE (T.sp.toNat + 208) 8 s).readLE up 8 = M0.readLE up 8 := by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hu0
  by_cases hn : n = 1
  · have hn' := hn
    subst hn
    janus_run [r3, r7, r9, r11, r5, r13, r15, r12, r14, hu0, hu0'] until [ku + 0x230]
    have hv : (if s < 64 then BitVec.ofNat 64 (M0.readLE up 8 * 2 ^ (s % 64)) else 0#64).toNat = (M0.readLE up 8 * 2 ^ s) % 2 ^ 64 := by
      have hs64 : s % 64 = s := Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), BitVec.toNat_ofNat, hs64]
    refine hK1 rfl _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp [setReg, hk]
    · have h0 := MemFrame.of_writeLE M (k := 8) remp (rs := [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)]) (a := T.sp.toNat + 288) (r := (T.sp.toNat + 288, T.sp.toNat + 296)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h1 := h0.writeLE (a := T.sp.toNat + 208) (k := 8) s (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
      exact h1.writeLE (a := T.sp.toNat + 80) (k := 8) (if s < 64 then BitVec.ofNat 64 (M0.readLE up 8 * 2 ^ (s % 64)) else 0#64).toNat (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
    · rw [Janus.Arm64.Memory.readLE_writeLE_self, hv]
      simp only [Nat.reducePow]
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    · intro j hj1 hj2
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt hremp
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
  · janus_run [r3, r7, r9, r11, r5, r13, r15, r12, r14, hu0, hu0'] until [ku + 0x20c]
    have hv : (if s < 64 then BitVec.ofNat 64 (M0.readLE up 8 * 2 ^ (s % 64)) else 0#64).toNat = (M0.readLE up 8 * 2 ^ s) % 2 ^ 64 := by
      have hs64 : s % 64 = s := Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega), BitVec.toNat_ofNat, hs64]
    refine hK2 hn _ _ _ (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp only [setReg]
      repeat' rw [if_neg (by omega)]
    · have h0 := MemFrame.of_writeLE M (k := 8) remp (rs := [(T.sp.toNat + 80, T.sp.toNat + 216), (T.sp.toNat + 288, T.sp.toNat + 296)]) (a := T.sp.toNat + 288) (r := (T.sp.toNat + 288, T.sp.toNat + 296)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h1 := h0.writeLE (a := T.sp.toNat + 208) (k := 8) s (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h2 := h1.writeLE (a := T.sp.toNat + 80) (k := 8) (if s < 64 then BitVec.ofNat 64 (M0.readLE up 8 * 2 ^ (s % 64)) else 0#64).toNat (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h3 := h2.writeLE (a := T.sp.toNat + 200) (k := 8) (n - 1) (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
      have h4 := h3.writeLE (a := T.sp.toNat + 152) (k := 8) (ulen + 1) (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
      exact h4.writeLE (a := T.sp.toNat + 192) (k := 8) (64 - s) (r := (T.sp.toNat + 80, T.sp.toNat + 216)) (by simp) (by simp <;> omega) (by simp <;> omega)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_writeLE_self, hv]
      simp only [Nat.reducePow]
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    · intro j hj1 hj2
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt hremp
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by omega)
    · intro j hj
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]


set_option maxHeartbeats 8000000 in
theorem by1tail (T : State) (ret : W64) (Q : State → Prop) (Mc : Memory) (R : Nat → W64) (fl : Flags)
    (remp s r1 x29 x30 : Nat) (hs : s ≤ 63) (hr1 : r1 < 2 ^ 64) (hx30a : x30 % 4 = 0) (hx30b : x30 < 2 ^ 56)
    (hal : T.sp.toNat % 16 = 0) (hsp : 8 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hMc : Mc.accessible (T.sp.toNat - 8) 304 true = true)
    (hremb : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ Mc.accessible remp 32 true = true ∧ (remp + 32 ≤ T.sp.toNat - 8 ∨ T.sp.toNat + 296 ≤ remp))
    (hremp : remp < 2 ^ 64)
    (r0 : R 0 = BitVec.ofNat 64 r1)
    (hs_rem : Mc.readLE (T.sp.toNat + 288) 8 = remp) (hs_s : Mc.readLE (T.sp.toNat + 208) 8 = s)
    (hs29 : Mc.readLE (T.sp.toNat - 8) 8 = x29) (hs30 : Mc.readLE T.sp.toNat 8 = x30)
    (hQ : ∀ (R' : Nat → W64) (fl' : Flags) (Mf : Memory), R' 29 = BitVec.ofNat 64 x29 → R' 30 = BitVec.ofNat 64 x30 →
      (∀ i, i ∉ [0, 1, 7, 29, 30] → R' i = R i) →
      (remp ≠ 0 → Mf.readLE remp 8 = r1 / 2 ^ s ∧ Mf.readLE (remp + 8) 8 = 0 ∧ Mf.readLE (remp + 16) 8 = 0 ∧ Mf.readLE (remp + 24) 8 = 0 ∧
        MemFrame Mc Mf [(remp, remp + 32)]) → (remp = 0 → Mf = Mc) →
      Q { T with regs := R', sp := T.sp + 224#64, pc := BitVec.ofNat 64 x30, flags := fl', mem := Mf }) :
    ReachesRet Extracted.program (BitVec.ofNat 64 x30) { T with regs := R, pc := BitVec.ofNat 64 by1ret, flags := fl, mem := Mc } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : by1ret
  simp only [hh1]
  by_cases hr0 : remp = 0
  · subst hr0
    janus_run [r0, hs_rem, hs_s, hs29, hs30]
    refine hQ _ _ _ (by simp [setReg]) (by simp [setReg]) ?_ (fun h => absurd rfl h) (fun _ => rfl)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
  · obtain ⟨hb, ha, hd⟩ := hremb hr0
    janus_run [r0, hs_rem, hs_s, hs29, hs30]
    have hsh := Fv256.Arm64.Shift.shr_val' r1 s hs hr1
    refine hQ _ _ _ (by simp [setReg]) (by simp [setReg]) ?_ (fun _ => ?_) (fun h => absurd h hr0)
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp only [setReg]
      repeat' rw [if_neg (by omega)]
    · have hq : r1 / 2 ^ s < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hr1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [hsh]; simp only [Nat.reducePow]; exact Nat.mod_eq_of_lt hq
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      · have h0 := MemFrame.of_writeLE Mc (k := 8) 0 (rs := [(remp, remp + 32)]) (a := remp + 16) (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
        have h1 := h0.writeLE (a := remp + 24) (k := 8) 0 (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
        have h2 := h1.writeLE (a := remp) (k := 8) (if s < 64 then BitVec.ofNat 64 r1 >>> (s % 64) else 0#64).toNat (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)
        exact h2.writeLE (a := remp + 8) (k := 8) 0 (r := (remp, remp + 32)) (by simp) (by simp <;> omega) (by simp <;> omega)


set_option maxHeartbeats 8000000 in
theorem rem_loop (T : State) (ret : W64) (Q : State → Prop) (remp n ulen s : Nat) (M0 : Memory) (R0 : Nat → W64)
    (hn1 : 2 ≤ n) (hn4 : n ≤ 4) (hnu : n ≤ ulen) (hul : ulen ≤ 8) (hs : s ≤ 63)
    (hremb : remp + 32 ≤ 2 ^ 48) (hMr : M0.accessible remp 32 true = true)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hMu : M0.accessible (T.sp.toNat + 80) 72 true = true)
    (hdisj : remp + 32 ≤ T.sp.toNat + 80 ∨ T.sp.toNat + 152 ≤ remp)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags) (M' : Memory), R' 5 = BitVec.ofNat 64 (n - 1) → (∀ k, k ∉ [5, 6, 7, 8, 9] → R' k = R0 k) →
      MemFrame M0 M' [(remp, remp + 8 * (n - 1))] →
      (∀ j, j < n - 1 → M'.readLE (remp + 8 * j) 8 = M0.readLE (T.sp.toNat + 80 + 8 * j) 8 / 2 ^ s + (M0.readLE (T.sp.toNat + 80 + 8 * (j + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64) →
      ReachesRet Extracted.program ret { T with regs := R', pc := BitVec.ofNat 64 rexit, flags := fl', mem := M' } Q) :
    ∀ t (R : Nat → W64) (fl : Flags) (M : Memory), t + 1 ≤ n → 
      R 0 = BitVec.ofNat 64 remp → R 1 = BitVec.ofNat 64 s → R 2 = BitVec.ofNat 64 (n - 1) → R 3 = BitVec.ofNat 64 (64 - s) →
      R 4 = BitVec.ofNat 64 (ulen + 1) → R 5 = BitVec.ofNat 64 (n - 1 - t) → (∀ k, k ∉ [5, 6, 7, 8, 9] → R k = R0 k) →
      MemFrame M0 M [(remp, remp + 8 * (n - 1))] → 
      (∀ j, j < n - 1 - t → M.readLE (remp + 8 * j) 8 = M0.readLE (T.sp.toNat + 80 + 8 * j) 8 / 2 ^ s + (M0.readLE (T.sp.toNat + 80 + 8 * (j + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64) →
      ReachesRet Extracted.program ret { T with regs := R, pc := BitVec.ofNat 64 rhead, flags := fl, mem := M } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : rhead
  janus_eval_nat hh2 : rexit
  simp only [hh2] at hK
  intro t
  induction t with
  | zero =>
    intro R fl M ht r0 r1 r2 r3 r4 r5 hRu hfr hdn
    simp only [hh1]
    janus_run [r5, r2] until [ku + 0x2c4]
    refine hK _ _ _ (by rw [r5]; simp) hRu hfr (fun j hj => hdn j (by omega))
  | succ t ih =>
    intro R fl M ht r0 r1 r2 r3 r4 r5 hRu hfr hdn
    simp only [hh1]
    have hMa : M.accessible (T.sp.toNat + 80) 72 true = true := by rw [hfr.accessible]; exact hMu
    have hMr' : M.accessible remp 32 true = true := by rw [hfr.accessible]; exact hMr
    janus_run [r0, r1, r2, r3, r4, r5] until [ku + 0x2a0, ku + 0x2c4]
    have hi1 : n - 1 - (t + 1) + 1 = n - 1 - t := by omega
    have hl : ∀ k, M0.readLE (T.sp.toNat + 80 + 8 * k) 8 < 2 ^ 64 := fun k => by
      have := Janus.Arm64.Memory.readLE_lt M0 (T.sp.toNat + 80 + 8 * k) 8; simpa using this
    have hval := Fv256.Arm64.Shift.rem_val (M0.readLE (T.sp.toNat + 80 + 8 * (n - 1 - (t + 1) + 1)) 8) (M0.readLE (T.sp.toNat + 80 + 8 * (n - 1 - (t + 1))) 8) s hs (hl _) (hl _)
    have hadr : T.sp.toNat + (80 + (n - 1 - (t + 1)) * 8) = T.sp.toNat + 80 + 8 * (n - 1 - (t + 1)) := by omega
    rw [hadr]
    refine ih _ _ _ (by omega) (by simp [setReg, r0]) (by simp [setReg, r1]) (by simp [setReg, r2]) (by simp [setReg, r3]) (by simp [setReg, r4]) ?_ ?_ ?_ ?_
    · simp only [setReg]; simp; bv_omega
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp only [setReg]
      repeat' rw [if_neg (by omega)]
      exact hRu k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    · exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
    · intro j hj
      by_cases hji : j = n - 1 - (t + 1)
      · subst hji
        rw [show remp + (n - 1 - (t + 1)) * 8 = remp + 8 * (n - 1 - (t + 1)) by omega, Janus.Arm64.Memory.readLE_writeLE_self,
          Nat.or_comm, hval]
        simp only [Nat.reducePow]
        exact Nat.mod_eq_of_lt (Fv256.Arm64.Shift.rem_lt _ _ s hs (hl _))
      · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hdn j (by omega)


set_option maxHeartbeats 8000000 in
theorem kntail (T : State) (ret : W64) (Q : State → Prop) (Mc : Memory) (R : Nat → W64) (fl : Flags)
    (remp n ulen s x29 x30 : Nat) (hn1 : 2 ≤ n) (hn4 : n ≤ 4) (hnu : n ≤ ulen) (hul : ulen ≤ 8) (hs : s ≤ 63)
    (hx30a : x30 % 4 = 0) (hx30b : x30 < 2 ^ 56)
    (hal : T.sp.toNat % 16 = 0) (hsp : 120 ≤ T.sp.toNat) (hspb : T.sp.toNat + 296 ≤ 2 ^ 48)
    (hMc : Mc.accessible (T.sp.toNat - 8) 304 true = true)
    (hremb : remp ≠ 0 → remp + 32 ≤ 2 ^ 48 ∧ Mc.accessible remp 32 true = true ∧ (remp + 32 ≤ T.sp.toNat - 8 ∨ T.sp.toNat + 296 ≤ remp))
    (hremp : remp < 2 ^ 64)
    (hs_rem : Mc.readLE (T.sp.toNat + 288) 8 = remp) (hs_s : Mc.readLE (T.sp.toNat + 208) 8 = s)
    (hs_n : Mc.readLE (T.sp.toNat + 200) 8 = n - 1) (hs_u : Mc.readLE (T.sp.toNat + 152) 8 = ulen + 1)
    (hs_c : Mc.readLE (T.sp.toNat + 192) 8 = 64 - s)
    (hs29 : Mc.readLE (T.sp.toNat - 8) 8 = x29) (hs30 : Mc.readLE T.sp.toNat 8 = x30)
    (hQ : ∀ (R' : Nat → W64) (fl' : Flags) (Mf : Memory), R' 29 = BitVec.ofNat 64 x29 → R' 30 = BitVec.ofNat 64 x30 →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 29, 30] → R' i = R i) →
      (remp ≠ 0 → (∀ j, j < n - 1 → Mf.readLE (remp + 8 * j) 8 = Mc.readLE (T.sp.toNat + 80 + 8 * j) 8 / 2 ^ s + (Mc.readLE (T.sp.toNat + 80 + 8 * (j + 1)) 8 * 2 ^ (64 - s)) % 2 ^ 64) ∧
        Mf.readLE (remp + 8 * (n - 1)) 8 = Mc.readLE (T.sp.toNat + 80 + 8 * (n - 1)) 8 / 2 ^ s ∧ MemFrame Mc Mf [(remp, remp + 8 * n)]) →
      (remp = 0 → Mf = Mc) →
      Q { T with regs := R', sp := T.sp + 224#64, pc := BitVec.ofNat 64 x30, flags := fl', mem := Mf }) :
    ReachesRet Extracted.program (BitVec.ofNat 64 x30) { T with regs := R, pc := BitVec.ofNat 64 knret, flags := fl, mem := Mc } Q := by
  have hcode := ku_lt
  janus_eval_nat hh1 : knret
  simp only [hh1]
  by_cases hr0 : remp = 0
  · subst hr0
    janus_run [hs_rem, hs29, hs30]
    refine hQ _ _ _ (by simp [setReg]) (by simp [setReg]) ?_ (fun h => absurd rfl h) (fun _ => rfl)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setReg]
    repeat' rw [if_neg (by omega)]
  · obtain ⟨hb, ha, hd⟩ := hremb hr0
    janus_run [hs_rem, hs_s, hs_n, hs_u, hs_c, hs29, hs30] until [ku + 0x2a0]
    refine rem_loop T (BitVec.ofNat 64 x30) Q remp n ulen s Mc _ hn1 hn4 hnu hul hs hb ha hal hsp hspb
      (Janus.Arm64.Memory.accessible_mono _ hMc (by omega) (by omega)) (by omega) ?hK (n - 1) _ fl Mc (by omega)
      (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) ?_ (fun k hk => rfl) (MemFrame.refl _ _) ?_
    case hK =>
      intro R' fl' M' r5' hRu' hfr' hdn'
      janus_eval_nat hh2 : rexit
      simp only [hh2]
      have hMa' : M'.accessible (T.sp.toNat - 8) 304 true = true := by rw [hfr'.accessible]; exact hMc
      have hMr' : M'.accessible remp 32 true = true := by rw [hfr'.accessible]; exact ha
      have hu1 : M'.readLE (T.sp.toNat + 80 + 8 * (n - 1)) 8 = Mc.readLE (T.sp.toNat + 80 + 8 * (n - 1)) 8 :=
        hfr'.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
      have q0 : R' 0 = BitVec.ofNat 64 remp := (hRu' 0 (by simp)).trans (by simp [setReg])
      have q1 : R' 1 = BitVec.ofNat 64 s := (hRu' 1 (by simp)).trans (by simp [setReg])
      have q2 : R' 2 = BitVec.ofNat 64 (n - 1) := (hRu' 2 (by simp)).trans (by simp [setReg])
      have q3 : R' 3 = BitVec.ofNat 64 (64 - s) := (hRu' 3 (by simp)).trans (by simp [setReg])
      have q4 : R' 4 = BitVec.ofNat 64 (ulen + 1) := (hRu' 4 (by simp)).trans (by simp [setReg])
      janus_run [r5', q0, q1, q2, q3, q4, hs_rem, hs_s, hs_n, hs_u, hs_c, hs29, hs30, hu1]
      have hlt : Mc.readLE (T.sp.toNat + 80 + 8 * (n - 1)) 8 < 2 ^ 64 := by
        have := Janus.Arm64.Memory.readLE_lt Mc (T.sp.toNat + 80 + 8 * (n - 1)) 8; simpa using this
      have hsh := Fv256.Arm64.Shift.shr_val' _ s hs hlt
      have hadr : T.sp.toNat + (80 + (n - 1) * 8) = T.sp.toNat + 80 + 8 * (n - 1) := by omega
      rw [hadr]
      refine hQ _ _ _ (by simp [setReg]) (by simp [setReg]) ?_ (fun _ => ⟨?_, ?_, ?_⟩) (fun h => absurd h hr0)
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp only [setReg]
        repeat' rw [if_neg (by omega)]
        rw [hRu' i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)]
        simp only [setReg]
        repeat' rw [if_neg (by omega)]
      · intro j hj
        rw [show remp + (n - 1) * 8 = remp + 8 * (n - 1) by omega]
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hdn' j hj
      · rw [show remp + (n - 1) * 8 = remp + 8 * (n - 1) by omega, Janus.Arm64.Memory.readLE_writeLE_self, hsh]
        simp only [Nat.reducePow]
        exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt)
      · have hm := hfr'.mono (rs' := [(remp, remp + 8 * n)]) (by intro a n' h; simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
        exact hm.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
    · simp [setReg]
    · intro j hj; omega

end Fv256.Arm64.UdivremA
