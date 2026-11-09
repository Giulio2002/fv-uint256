import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.UdivMathB
import Fv256.Proofs.Arm64.By1Math
import Fv256.Proofs.Arm64.Div64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-!
# `uint256.udivremBy1(quot, u []uint64, d uint64) (rem uint64)` (arm64)

`by1_summary`: for a normalised single-word divisor `2^63 <= d`, `2 <= n = len(u) < 2^20`, `len(quot) >= n - 1`,
`u[n-1] < d`, writable `quot[0..n-1)` and readable `u[0..n)` disjoint from each other and from the stack window the
call uses, the call returns `rem < d` in `X0` with `wv u n = d * wv quot' (n-1) + rem`, changes memory only in
`quot[0..n-1)` and the call's stack window, and preserves `SP`, `X18`, `X28`..`X30` and every register outside
`X0..X12, X16`.  Same statement shape as the amd64 `Fv256.Amd64.DivWork2.by1_summary`.  The reciprocal comes from the
`math/bits.Div64` summary (`Fv256.Arm64.Div64.div64_summary`); the loop is `by1_loop`.
-/

namespace Fv256.Arm64.By1

abbrev by1 : Nat := segAddr Fv256.Arm64.ChainProg.program "github.com/holiman/uint256.udivremBy1"
abbrev bhead : Nat := by1 + 0x90
abbrev d64 : Nat := segAddr Fv256.Arm64.ChainProg.program "math/bits.Div64"

theorem ofNat_toNat' (x : W64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

theorem rr_mono {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop} (h : ReachesRet p ret s Q)
    (hQ : ∀ S, Q S → Q' S) : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hp, hq⟩ := h
  exact ⟨k, s', hs, hp, hQ _ hq⟩

theorem rr_mem_congr {p : Program} {ret : W64} {Q : State → Prop} (S : State) (M2 : Memory)
    (h : ReachesRet p ret { S with mem := M2 } Q) (hm : S.mem = M2) : ReachesRet p ret S Q := by
  cases S; simp only at hm; subst hm; exact h

theorem by1_lt : by1 + 0x200 < 2 ^ 47 := by decide

theorem bv_toNat_ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h


set_option maxHeartbeats 16000000 in
theorem by1_loop (s0 T : State) (q u n d v : Nat) (hn : 2 ≤ n) (hn2 : n < 2 ^ 20)
    (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / d)
    (hq : (s0.regs 0).toNat = q) (hu : (s0.regs 3).toNat = u) (hqlen : n - 1 ≤ (s0.regs 1).toNat)
    (hd : (s0.regs 6).toNat = d) (hal : s0.sp.toNat % 16 = 0) (hsp : 88 ≤ s0.sp.toNat) (hspb : s0.sp.toNat + 64 ≤ 2 ^ 48)
    (hspa : s0.mem.accessible (s0.sp.toNat - 88) (88 + 64) true = true)
    (hqa : s0.mem.accessible q (8 * (n - 1)) true = true) (hqb : q + 8 * (n - 1) ≤ 2 ^ 48)
    (hua : s0.mem.accessible u (8 * n) false = true) (hub : u + 8 * n ≤ 2 ^ 48)
    (hqu : q + 8 * (n - 1) ≤ u ∨ u + 8 * n ≤ q)
    (hqs : q + 8 * (n - 1) ≤ s0.sp.toNat - 88 ∨ s0.sp.toNat + 64 ≤ q)
    (hus : u + 8 * n ≤ s0.sp.toNat - 88 ∨ s0.sp.toNat + 64 ≤ u)
    (h30a : (s0.regs 30).toNat % 4 = 0) (h30b : (s0.regs 30).toNat < 2 ^ 56) :
    ∀ k (rem : Nat) (R : Nat → W64) (fl : Flags) (M : Memory), k ≤ n - 1 → rem < d →
      R 0 = BitVec.ofNat 64 v → R 1 = BitVec.ofNat 64 u → R 2 = BitVec.ofNat 64 rem → R 3 = BitVec.ofNat 64 k - 1 →
      R 4 = s0.regs 1 → R 5 = BitVec.ofNat 64 q → R 6 = BitVec.ofNat 64 d →
      (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 29, 30] → R i = s0.regs i) →
      R 29 = s0.sp - 56#64 →
      Fv256.B.wv s0.mem (u + 8 * k) (n - k) = d * Fv256.B.wv M (q + 8 * k) (n - 1 - k) + rem →
      (∀ i, i < n → M.readLE (u + 8 * i) 8 = s0.mem.readLE (u + 8 * i) 8) →
      MemFrame s0.mem M [(q, q + 8 * (n - 1)), (s0.sp.toNat - 88, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 24),
        (s0.sp.toNat + 32, s0.sp.toNat + 48), (s0.sp.toNat + 56, s0.sp.toNat + 64)] →
      M.readLE (s0.sp.toNat - 56) 8 = (s0.regs 29).toNat → M.readLE (s0.sp.toNat - 48) 8 = (s0.regs 30).toNat →
      ReachesRet Fv256.Arm64.ChainProg.program (s0.regs 30)
        { T with regs := R, sp := s0.sp - 48#64, pc := BitVec.ofNat 64 bhead, flags := fl, mem := M }
        (fun S' => ∃ (rem' : Nat) (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { T with regs := R', sp := s0.sp, pc := s0.regs 30, flags := fl', mem := M' } ∧
          R' 0 = BitVec.ofNat 64 rem' ∧
          (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → R' i = s0.regs i) ∧
          rem' < d ∧ Fv256.B.wv s0.mem u n = d * Fv256.B.wv M' q (n - 1) + rem' ∧
          MemFrame s0.mem M' [(q, q + 8 * (n - 1)), (s0.sp.toNat - 88, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 24),
            (s0.sp.toNat + 32, s0.sp.toNat + 48), (s0.sp.toNat + 56, s0.sp.toNat + 64)]) := by
  have hcode := by1_lt
  janus_eval_nat hh : bhead
  have hspn : (s0.sp - 48#64).toNat = s0.sp.toNat - 48 := by
    rw [BitVec.toNat_sub, bv_toNat_ofNat_lt 48 (by omega)]; omega
  have hlr30 : BitVec.ofNat 64 (s0.regs 30).toNat = s0.regs 30 := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (s0.regs 30).isLt
  have hal48 : (s0.sp - 48#64).toNat % 16 = 0 := by rw [hspn]; omega
  intro k
  induction k with
  | zero =>
    intro rem R fl M hk hrem h0 h1 h2 h3 h4 h5 h6 hRu h29 hI hu' hfr hr29 hr30
    simp only [hh]
    have hmsb : (BitVec.ofNat 64 0 - (1 : BitVec 64)).getLsbD 63 = true := by decide
    have hMa : M.accessible (s0.sp.toNat - 88) (88 + 64) true = true := by rw [hfr.accessible]; exact hspa
    have hr29' : M.readLE ((s0.sp - 48#64).toNat - 8) 8 = (s0.regs 29).toNat := by rw [hspn]; exact hr29
    have hr30' : M.readLE ((s0.sp - 48#64).toNat) 8 = (s0.regs 30).toNat := by rw [hspn]; exact hr30
    have hMa2 : M.accessible ((s0.sp - 48#64).toNat - 8) 16 true = true := by
      rw [hspn]; exact Janus.Arm64.Memory.accessible_mono _ hMa (by omega) (by omega)
    have hMa3 : M.accessible ((s0.sp - 48#64).toNat) 8 true = true := by
      rw [hspn]; exact Janus.Arm64.Memory.accessible_mono _ hMa (by omega) (by omega)
    janus_run [h0, h1, h2, h3, h4, h5, h6, h29, hmsb, hr29', hr30', hspn, hlr30, hr29, hr30]
    refine ⟨rem, _, _, M, rfl, ?_, ?_, hrem, ?_, hfr⟩
    · simp [setReg]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp only [setReg]
      by_cases h30' : i = 30
      · subst h30'; simp
      by_cases h29' : i = 29
      · subst h29'; simp
      rw [if_neg h30', if_neg h29', if_neg (by omega)]
      exact hRu i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
    · simpa using hI
  | succ k ih =>
    intro rem R fl M hk hrem h0 h1 h2 h3 h4 h5 h6 hRu h29 hI hu' hfr hr29 hr30
    simp only [hh]
    have hj : BitVec.ofNat 64 (k + 1) - (1 : BitVec 64) = BitVec.ofNat 64 k := by bv_omega
    rw [hj] at h3
    have hmsb : (BitVec.ofNat 64 k).getLsbD 63 = false := by
      rw [← BitVec.testBit_toNat]
      exact Nat.testBit_lt_two_pow (by rw [BitVec.toNat_ofNat]; omega)
    have hMa : M.accessible (s0.sp.toNat - 88) (88 + 64) true = true := by rw [hfr.accessible]; exact hspa
    have hspn' : (s0.sp - 48#64).toNat = s0.sp.toNat - 48 := hspn
    have hMq : M.accessible q (8 * (n - 1)) true = true := by rw [hfr.accessible]; exact hqa
    have hMu : M.accessible u (8 * n) false = true := by rw [hfr.accessible]; exact hua
    janus_run [h0, h1, h2, h3, h4, h5, h6, h29, hmsb, hu', hspn] until [by1 + 0x90]
    have hukB : s0.mem.readLE (u + k * 8) 8 < 2 ^ 64 := by
      have := Janus.Arm64.Memory.readLE_lt s0.mem (u + k * 8) 8; simpa using this
    have hvB : v < 2 ^ 64 := Fv256.B.recip_lt d v hd1 hv
    have hremB : rem < 2 ^ 64 := by omega
    generalize huk : s0.mem.readLE (u + k * 8) 8 = uk at *
    have hXv := Fv256.Arm64.By1Math.qh_val v rem uk hvB hremB hukB
    generalize hQH : (addWithCarry (BitVec.ofNat 64 rem)
        (BitVec.extractLsb' 64 64 (BitVec.setWidth 128 (BitVec.ofNat 64 v) * BitVec.setWidth 128 (BitVec.ofNat 64 rem)))
        (addWithCarry (BitVec.ofNat 64 v * BitVec.ofNat 64 rem) (BitVec.ofNat 64 uk) false).snd.c).fst = X at *
    have hcorr := Fv256.B.div2by1_correct (2 ^ 64) d (v + 2 ^ 64) rem uk (by omega) hd2 (by rw [← hv]) (by omega) hukB
    have hsub : v + 2 ^ 64 - 2 ^ 64 = v := by omega
    rw [hsub] at hcorr
    refine rr_mem_congr _ (M.writeLE (q + 8 * k) 8 (Fv256.B.div2by1 (2 ^ 64) d v rem uk).1) ?main ?memeq
    case memeq =>
      rw [show q + k * 8 = q + 8 * k by omega]
      apply Fv256.B.writeLE_val_congr
      exact Fv256.Arm64.By1Math.step_quot v rem uk d X hvB hremB hukB (by omega) hXv
    case main =>
      refine ih (Fv256.B.div2by1 (2 ^ 64) d v rem uk).2 _ _ _ (by omega) ?hrem' ?r0 ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?ru ?r29 ?hI ?hu ?hfr ?hr29 ?hr30
      case hrem' => rw [hcorr]; exact Nat.mod_lt _ (by omega)
      case r0 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h0]
      case r1 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h1]
      case r2 =>
        have e := Fv256.Arm64.By1Math.step_rem v rem uk d X hvB hremB hukB (by omega) hXv
        simp (config := { decide := true }) only [setReg, ↓reduceIte]
        exact e
      case r3 => simp (config := { decide := true }) only [setReg, ↓reduceIte]; rfl
      case r4 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h4]
      case r5 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h5]
      case r6 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h6]
      case ru =>
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp only [setReg]
        repeat' rw [if_neg (by omega)]
        exact hRu i (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)
      case r29 => simp (config := { decide := true }) only [setReg, ↓reduceIte, h29]
      case hI =>
        have hQlt : (rem * 2 ^ 64 + uk) / d < 2 ^ 64 := by
          apply Nat.div_lt_of_lt_mul
          have : (rem + 1) * 2 ^ 64 ≤ d * 2 ^ 64 := Nat.mul_le_mul_right _ hrem
          rw [Nat.add_mul] at this
          rw [Nat.mul_comm d]; omega
        have hT := Nat.div_add_mod (rem * 2 ^ 64 + uk) d
        have e1 : n - k = (n - (k + 1)) + 1 := by omega
        have e2 : n - 1 - k = (n - 1 - (k + 1)) + 1 := by omega
        have ea : u + 8 * (k + 1) = u + 8 * k + 8 := by omega
        have eb : q + 8 * (k + 1) = q + 8 * k + 8 := by omega
        rw [ea, eb] at hI
        rw [e1, e2, Fv256.B.wv_succ, Fv256.B.wv_succ, Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (Or.inl (by omega)),
          Janus.Arm64.Memory.readLE_writeLE_self]
        rw [show u + 8 * k = u + k * 8 by omega, huk, hcorr]
        simp only [Nat.reducePow, Nat.mod_eq_of_lt hQlt]
        generalize Fv256.B.wv M (q + 8 * k + 8) (n - 1 - (k + 1)) = W at *
        grind
      case hu =>
        intro i hi
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hu' i hi
      case hfr => exact hfr.writeLE _ (List.mem_cons_self ..) (by omega) (by omega)
      case hr29 =>
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hr29
      case hr30 =>
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hr30



set_option maxHeartbeats 16000000 in
theorem by1_summary :
    Summary Fv256.Arm64.ChainProg.program by1
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 48 ∧ StackOK s 88 64 ∧
        2 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat < 2 ^ 20 ∧ 2 ^ 63 ≤ (s.regs 6).toNat ∧
        (s.regs 4).toNat - 1 ≤ (s.regs 1).toNat ∧
        (s.mem.accessible (s.regs 0).toNat (8 * ((s.regs 4).toNat - 1)) true = true ∧ (s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1) ≤ 2 ^ 48) ∧
        (s.mem.accessible (s.regs 3).toNat (8 * (s.regs 4).toNat) false = true ∧ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ 2 ^ 48) ∧
        ((s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1) ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ (s.regs 0).toNat) ∧
        ((s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1) ≤ s.sp.toNat - 88 ∨ s.sp.toNat + 64 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * (s.regs 4).toNat ≤ s.sp.toNat - 88 ∨ s.sp.toNat + 64 ≤ (s.regs 3).toNat) ∧
        s.mem.readLE ((s.regs 3).toNat + 8 * ((s.regs 4).toNat - 1)) 8 < (s.regs 6).toNat ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 88 ∨ s.sp.toNat + 64 ≤ (s.regs 28).toNat + 16))
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        (s'.regs 0).toNat < (s.regs 6).toNat ∧
        Fv256.B.wv s.mem (s.regs 3).toNat (s.regs 4).toNat =
          (s.regs 6).toNat * Fv256.B.wv s'.mem (s.regs 0).toNat ((s.regs 4).toNat - 1) + (s'.regs 0).toNat ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → s'.regs i = s.regs i) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1)),
          (s.sp.toNat - 88, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat + 32, s.sp.toNat + 48),
          (s.sp.toNat + 56, s.sp.toNat + 64)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hn1, hn2, hd1, hql, ⟨hqa, hqb⟩, ⟨hua, hub⟩, hqu, hqs, hus, htop, hgs⟩
  have hcode := by1_lt
  have hnot : (~~~s.regs 6).toNat < (s.regs 6).toNat := by rw [BitVec.toNat_not]; omega
  have hmsb0 : (s.regs 4 - 2#64).getLsbD 63 = false := by
    rw [← BitVec.testBit_toNat]
    apply Nat.testBit_lt_two_pow
    rw [BitVec.toNat_sub, bv_toNat_ofNat_lt 2 (by omega)]; omega
  janus_run [hmsb0] until [by1 + 0x90] calls [hc := Fv256.Arm64.Div64.div64_summary]
  have cx0 : (s'.regs 0).toNat = ((~~~s.regs 6).toNat * 18446744073709551616 + 18446744073709551615) / (s.regs 6).toNat := ‹_›
  have cu := ‹∀ i : Nat, ¬ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → _›
  have cf := ‹MemFrame _ s'.mem _›
  have hd2 : (s.regs 6).toNat < 2 ^ 64 := (s.regs 6).isLt
  have hvrel : (s'.regs 0).toNat + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / (s.regs 6).toNat := by
    rw [cx0, BitVec.toNat_not]
    have hd0 : 0 < (s.regs 6).toNat := by omega
    have e : (2 ^ 64 * 2 ^ 64 - 1 : Nat) = (18446744073709551615 - (s.regs 6).toNat) * 18446744073709551616 + 18446744073709551615 +
        (s.regs 6).toNat * 18446744073709551616 := by
      have : (s.regs 6).toNat * 18446744073709551616 ≤ 2 ^ 64 * 2 ^ 64 - 1 := by
        have := Nat.mul_le_mul_right 18446744073709551616 (show (s.regs 6).toNat ≤ 18446744073709551615 by omega)
        omega
      have e2 : (18446744073709551615 - (s.regs 6).toNat) * 18446744073709551616 + (s.regs 6).toNat * 18446744073709551616 = 18446744073709551615 * 18446744073709551616 := by
        rw [← Nat.add_mul]; congr 1; omega
      omega
    rw [e, Nat.mul_comm (s.regs 6).toNat 18446744073709551616, Nat.add_mul_div_right _ _ hd0]
  have hvB : (s'.regs 0).toNat < 2 ^ 64 := (s'.regs 0).isLt
  have hn2' : (s.regs 4).toNat - 1 + 1 = (s.regs 4).toNat := by omega
  -- the frame of everything the prologue and the call wrote
  have hpro := MemFrame.of_writeLE s.mem (k := 8) (BitVec.toNat (s.regs 30)) (rs := [((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1)),
      (s.sp.toNat - 88, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat + 32, s.sp.toNat + 48),
      (s.sp.toNat + 56, s.sp.toNat + 64)]) (a := s.sp.toNat - 48) (r := (s.sp.toNat - 88, s.sp.toNat - 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  have hpro := (hpro.writeLE (a := s.sp.toNat - 56) (k := 8) (BitVec.toNat (s.regs 29)) (r := (s.sp.toNat - 88, s.sp.toNat - 8)) (by simp) (by simp <;> omega) (by simp <;> omega)).writeLE
      (a := s.sp.toNat + 56) (k := 8) (BitVec.toNat (s.regs 6)) (r := (s.sp.toNat + 56, s.sp.toNat + 64)) (by simp) (by simp <;> omega) (by simp <;> omega)
  have hpro := (hpro.writeLE (a := s.sp.toNat + 16) (k := 8) (BitVec.toNat (s.regs 1)) (r := (s.sp.toNat + 8, s.sp.toNat + 24)) (by simp) (by simp <;> omega) (by simp <;> omega)).writeLE
      (a := s.sp.toNat + 8) (k := 8) (BitVec.toNat (s.regs 0)) (r := (s.sp.toNat + 8, s.sp.toNat + 24)) (by simp) (by simp <;> omega) (by simp <;> omega)
  have hpro := (hpro.writeLE (a := s.sp.toNat + 32) (k := 8) (BitVec.toNat (s.regs 3)) (r := (s.sp.toNat + 32, s.sp.toNat + 48)) (by simp) (by simp <;> omega) (by simp <;> omega)).writeLE
      (a := s.sp.toNat + 40) (k := 8) (BitVec.toNat (s.regs 4)) (r := (s.sp.toNat + 32, s.sp.toNat + 48)) (by simp) (by simp <;> omega) (by simp <;> omega)
  have hpro := hpro.writeLE (a := s.sp.toNat - 16) (k := 8) (BitVec.toNat (s.regs 4) - 1) (r := (s.sp.toNat - 88, s.sp.toNat - 8)) (by simp) (by simp <;> omega) (by simp <;> omega)
  have hF := hpro.trans cf (rs'' := [((s.regs 0).toNat, (s.regs 0).toNat + 8 * ((s.regs 4).toNat - 1)),
      (s.sp.toNat - 88, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat + 32, s.sp.toNat + 48),
      (s.sp.toNat + 56, s.sp.toNat + 64)]) (by
    intro a n h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega)
  refine rr_mono (by1_loop s s' (s.regs 0).toNat (s.regs 3).toNat (s.regs 4).toNat (s.regs 6).toNat (s'.regs 0).toNat hn1 hn2 hd1 hd2 hvrel rfl rfl hql rfl hal hb ha hw hqa hqb hua hub hqu hqs hus h30a h30b ((s.regs 4).toNat - 1) (s.mem.readLE ((s.regs 3).toNat + 8 * ((s.regs 4).toNat - 1)) 8) _ _ _ (Nat.le_refl _) htop ?h0 ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?hRu ?h29 ?hI ?hu hF ?hr29 ?hr30) ?post
  case h0 => simp (config := { decide := true }) only [setReg, ↓reduceIte, ofNat_toNat']
  case h1 => simp (config := { decide := true }) only [setReg, ↓reduceIte, ofNat_toNat']
  case h2 =>
    simp (config := { decide := true }) only [setReg, ↓reduceIte]
    rw [Nat.mul_comm ((s.regs 4).toNat - 1) 8]
  case h3 =>
    simp (config := { decide := true }) only [setReg, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    bv_omega
  case h4 => simp (config := { decide := true }) only [setReg, ↓reduceIte]
  case h5 => simp (config := { decide := true }) only [setReg, ↓reduceIte, ofNat_toNat']
  case h6 => simp (config := { decide := true }) only [setReg, ↓reduceIte, ofNat_toNat']
  case hRu =>
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [setReg]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [cu i (by simp; omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  case h29 =>
    simp only [setReg]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [cu 29 (by simp)]
    simp
  case hI =>
    rw [show (s.regs 4).toNat - ((s.regs 4).toNat - 1) = 1 by omega, show (s.regs 4).toNat - 1 - ((s.regs 4).toNat - 1) = 0 by omega]
    simp [Fv256.B.wv]
  case hu =>
    intro i hi
    exact hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  case hr29 =>
    rw [cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 29).isLt
  case hr30 =>
    rw [cf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 30).isLt
  case post =>
    intro S ⟨rem', R', fl', M', hS, h0', hRu', hlt, hwv, hfr'⟩
    subst hS
    have hr0 : (R' 0).toNat = rem' := by rw [h0', bv_toNat_ofNat_lt _ (by omega)]
    refine ⟨rfl, rfl, hRu' 28 (by simp), hRu' 29 (by simp), hRu' 30 (by simp), hRu' 18 (by simp), ?_, ?_, hRu', hfr'⟩
    · show (R' 0).toNat < _
      rw [hr0]; exact hlt
    · show _ = _ * _ + (R' 0).toNat
      rw [hr0]; exact hwv


end Fv256.Arm64.By1
