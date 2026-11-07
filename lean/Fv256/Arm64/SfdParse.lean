import Fv256.Spec
import Fv256.Util
import Fv256.HexLemmas
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdProg

/-!
# `internal/strconv.ParseUint(s, 10, 64)` on a string of 1 to 19 bytes (arm64)

The digit loop of `strconv.ParseUint` for `base = 10`, `bitSize = 64`: for at most 19 bytes the value cannot overflow
(`10^19 - 1 < 2^64`), so the result is the number when every byte is an ASCII digit, and the internal syntax error
otherwise.  The error values are the addresses of the constant `internal/strconv.Error` objects in read-only data
(`ErrSyntax` is the constant at `0xf5940`).  Over the library program `SfdProg.program`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.I

namespace Fv256.Arm64.SfdParse

abbrev ip : Nat := segAddr Fv256.Arm64.SfdProg.program "internal/strconv.ParseUint"
abbrev head : Nat := ip + 0x1bc

/-- the address of the `internal/strconv.ErrSyntax` constant (an `internal/strconv.Error`) -/
abbrev synAddr : Nat := 0xf5940
/-- the itab of `internal/strconv.Error` as an `error` -/
abbrev errItab : Nat := 0xf6920

def LoopQ (s : State) (M : Memory) (p len : Nat) (s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧ s'.mem = M ∧
  ((allDec (Fv256.C.bytesAt M p) 0 len ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 0 = 0 ∧ (s'.regs 1).toNat = errItab ∧ (s'.regs 2).toNat = synAddr))

theorem rr0 (x : BitVec 64) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight]
  simp [Nat.shiftLeft_eq, Nat.mul_mod_left]

theorem and255 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

set_option maxRecDepth 100000 in
theorem or32 (c : Nat) (hc : c < 256) : c ||| 32 = c + 32 * (1 - c / 32 % 2) := by
  revert c; decide

theorem dig64 (c : Nat) (h1 : 48 ≤ c) (h2 : c ≤ 57) :
    (BitVec.ofNat 64 c - 48#64).rotateRight 0 &&& 255#64 &&& 255#64 = BitVec.ofNat 64 (c - 48) := by
  rw [rr0]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat, and255, Nat.reducePow, Nat.reduceMod]
  omega

syntax "sfd_ex" : tactic
set_option hygiene false in
macro_rules | `(tactic| sfd_ex) => `(tactic| (
  exfalso
  clear ih hsS
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_add, hcm, hDm, hdg, hm10, rr0, and255, or32 c hc256, Bool.not_eq_false, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
  omega))

syntax "sfd_err" : tactic
set_option hygiene false in
macro_rules | `(tactic| sfd_err) => `(tactic| (
  unfold LoopQ
  refine ⟨rfl, ?_, ?_, ?_, rfl, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · simp [setReg_apply]
  · simp [setReg_apply, h28]
  · simp [setReg_apply, h18]
  · intro hall
    have hd := hall i (Nat.zero_le _) (by omega)
    simp only [Fv256.C.bytesAt, isDec, hc] at hd
    clear ih hsS hall
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or,
      hcm, rr0, and255, or32 c hc256, Bool.not_eq_false, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at *
    omega
  · simp [setReg_apply]
  · simp [setReg_apply]
  · simp [setReg_apply]
))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem loop (impl : List Segment) (s : State) (M : Memory) (p len : BitVec 64)
    (hL : 1 ≤ len.toNat) (hL2 : len.toNat ≤ 19)
    (hsa : M.accessible p.toNat len.toNat false = true) (hp : p.toNat + len.toNat ≤ 2 ^ 48)
    (hrM : M.readLE (s.sp.toNat - 48) 8 = (s.regs 30).toNat) (hbp : M.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat)
    (hl1 : (s.regs 30).toNat % 4 = 0) (hl2 : (s.regs 30).toNat < 2 ^ 48)
    (hal : s.sp.toNat % 16 = 0) (hsp : 56 ≤ s.sp.toNat) (hspa : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hacc : M.accessible (s.sp.toNat - 56) (56 + 16) true = true) :
    ∀ n (S : State) (i : Nat), n = len.toNat - i → i ≤ len.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 8 = BitVec.ofNat 64 i → S.regs 5 = len →
      S.regs 4 = p → S.regs 9 = BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) →
      S.regs 7 = 0x199999999999999a#64 → S.regs 6 = 10#64 → S.regs 3 = 0xffffffffffffffff#64 →
      S.regs 2 = 10#64 → S.regs 10 = 0#64 → S.sp = s.sp - 48#64 → S.regs 29 = s.sp - 56#64 →
      S.regs 30 = s.regs 30 → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = M →
      allDec (Fv256.C.bytesAt M p.toNat) 0 i →
      ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S (LoopQ s M p.toNat len.toNat) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i hn hi hpc h8 h5 h4 h9 h7 h6 h3 h2 h10 hsS h29 h30 h28 h18 hmem hdig
    have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by rw [BitVec.toNat_sub]; simp; omega
    have hsp56 : (s.sp - 56#64).toNat = s.sp.toNat - 56 := by
      rw [BitVec.toNat_sub]; simp; omega
    have hal48 : (s.sp - 48#64).toNat % 16 = 0 := by rw [hsp48]; omega
    have hof30 : BitVec.ofNat 64 (s.regs 30).toNat = s.regs 30 := by simp
    have hof29 : BitVec.ofNat 64 (s.regs 29).toNat = s.regs 29 := by simp
    have hl1 : Janus.Arm64.load M ((18446744073709551608 + BitVec.toNat (s.sp - 48#64)) % 18446744073709551616) 8 =
        .ok (M.readLE ((18446744073709551608 + BitVec.toNat (s.sp - 48#64)) % 18446744073709551616) 8) := by
      apply Janus.Arm64.load_eq_ok
      rw [hsp48]
      have : (18446744073709551608 + (s.sp.toNat - 48)) % 18446744073709551616 = s.sp.toNat - 56 := by omega
      rw [this]
      exact Memory.accessible_mono _ (Memory.accessible_weaken _ hacc) (by omega) (by omega)
    by_cases hlt' : i < len.toNat
    · obtain ⟨c, hc⟩ : ∃ c, M.readLE (p.toNat + i) 1 = c := ⟨_, rfl⟩
      have hc256 : c < 256 := by rw [← hc]; simpa using Janus.Arm64.Memory.readLE_lt M (p.toNat + i) 1
      have hcm : c % 18446744073709551616 = c := Nat.mod_eq_of_lt (by omega)
      janus_run [hsp48, hsp56, hl1, hrM, hbp, hof30, hof29, hc] until [ip + 0x220]
      all_goals first
        | (exfalso
           clear ih hsS
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or,
             hcm, rr0, and255, or32 c hc256, Bool.not_eq_false, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq, Bool.and_eq_true,
             Bool.not_eq_true', decide_eq_false_iff_not] at *
           omega)
        | skip
      all_goals (try sfd_err)
      have hdc : 48 ≤ c ∧ c ≤ 57 := by
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_and, BitVec.toNat_or,
          hcm, rr0, and255, or32 c hc256, Bool.not_eq_false, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq,
          Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at *
        omega
      have hD : decSum (Fv256.C.bytesAt M p.toNat) 0 i < 1000000000000000000 :=
        Nat.lt_of_lt_of_le (decSum_lt _ 0 i (by simpa using hdig)) (Nat.pow_le_pow_right (by decide) (by omega : i ≤ 18))
      have hDm : (decSum (Fv256.C.bytesAt M p.toNat) 0 i) % 18446744073709551616 = decSum (Fv256.C.bytesAt M p.toNat) 0 i :=
        Nat.mod_eq_of_lt (by omega)
      have hm10 : (BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) * 10#64).toNat =
          decSum (Fv256.C.bytesAt M p.toNat) 0 i * 10 := by
        simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hDm]
        exact Nat.mod_eq_of_lt (by omega)
      have hdg : (18446744073709551616 - 48 + c) % 18446744073709551616 % 256 = c - 48 := by omega
      janus_run [hsp48, hsp56, hl1, hrM, hbp, hof30, hof29, hc] until [head]
      all_goals (rw [dig64 c hdc.1 hdc.2] at *)
      all_goals (try sfd_ex)
      have hsuc : decSum (Fv256.C.bytesAt M p.toNat) 0 (i + 1) = decSum (Fv256.C.bytesAt M p.toNat) 0 i * 10 + (c - 48) := by
        simp only [decSum, Fv256.C.bytesAt, Nat.zero_add, hc]
      refine ih (len.toNat - (i + 1)) (by omega) _ (i + 1) rfl (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals (try (simp [setReg_apply, h8, h5, h4, h7, h6, h3, h2, h10, hsS, h29, h30, h28, h18, hmem]; done))
      all_goals try first
        | (simp only [setReg_apply]; first | rfl | decide | (simp only [head, ip]; decide))
        | (simp only [setReg_apply, Nat.reduceEqDiff, reduceIte]
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
           omega)
        | (simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, hsuc]
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hm10, hcm]
           omega)
      intro k hk hk'
      by_cases hki : k < i
      · exact hdig k hk hki
      · have hk2 : k = i := by omega
        subst hk2
        simp only [isDec, Fv256.C.bytesAt, hc]
        exact hdc
    · have hil : i = len.toNat := by omega
      subst hil
      have hD : decSum (Fv256.C.bytesAt M p.toNat) 0 len.toNat < 10 ^ 19 :=
        Nat.lt_of_lt_of_le (decSum_lt _ 0 _ (by simpa using hdig)) (Nat.pow_le_pow_right (by decide) hL2)
      janus_run [hsp48, hsp56, hl1, hrM, hbp, hof30, hof29]
      all_goals unfold LoopQ
      all_goals refine ⟨rfl, ?_, ?_, ?_, rfl, Or.inl ⟨hdig, ?_, ?_, ?_⟩⟩
      all_goals first
        | (simp [setReg_apply, h28]; done)
        | (simp [setReg_apply, h18]; done)
        | (simp only [setReg_apply, Nat.reduceEqDiff, reduceIte, BitVec.toNat_ofNat, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
        | skip

theorem rr_mono {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

def PuPre (p len : BitVec 64) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ GuardOK s 0 ∧ StackOK s 56 16 ∧
  s.regs 0 = p ∧ s.regs 1 = len ∧ s.regs 2 = 10#64 ∧ s.regs 3 = 64#64 ∧
  s.mem.accessible p.toNat len.toNat false = true ∧ p.toNat + len.toNat ≤ 2 ^ 48 ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 19 ∧
  (p.toNat + len.toNat ≤ s.sp.toNat - 56 ∨ s.sp.toNat + 16 ≤ p.toNat)

def PuPost (p len : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 56, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)] ∧
  ((allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧
      (s'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 0 = 0 ∧ (s'.regs 1).toNat = errItab ∧
      (s'.regs 2).toNat = synAddr))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem pu_sum (impl : List Segment) (p len : BitVec 64) :
    Summary (Fv256.Arm64.SfdProg.program.link impl) ip (PuPre p len) (PuPost p len) := by
  intro s hpc ⟨hl1, hl2, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, h0, h1, h2, h3, hsa, h48, hL, hL2, hdisj⟩
  subst h0 h1
  janus_run until [head]
  obtain ⟨M, hM⟩ : ∃ M, M = ((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 (BitVec.toNat (s.regs 30))).writeLE (BitVec.toNat s.sp - 56) 8
              (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 8) 8 (BitVec.toNat (s.regs 0)) := ⟨_, rfl⟩
  rw [← hM]
  have hbytes : ∀ k, k < (s.regs 1).toNat → Fv256.C.bytesAt M (s.regs 0).toNat k = Fv256.C.bytesAt s.mem (s.regs 0).toNat k := by
    intro k hk
    simp only [hM, Fv256.C.bytesAt]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hsum : decSum (Fv256.C.bytesAt M (s.regs 0).toNat) 0 (s.regs 1).toNat = decSum (Fv256.C.bytesAt s.mem (s.regs 0).toNat) 0 (s.regs 1).toNat :=
    decSum_congr _ _ 0 _ (fun k _ hk => hbytes k (by omega))
  have hall : allDec (Fv256.C.bytesAt M (s.regs 0).toNat) 0 (s.regs 1).toNat ↔ allDec (Fv256.C.bytesAt s.mem (s.regs 0).toNat) 0 (s.regs 1).toNat :=
    ⟨fun h k a b => by rw [← hbytes k (by omega)]; exact h k a b, fun h k a b => by rw [hbytes k (by omega)]; exact h k a b⟩
  refine rr_mono (loop impl s M (s.regs 0) (s.regs 1) hL hL2 ?_ h48 ?_ ?_ hl1 hl2 hal hb ha ?_ (s.regs 1).toNat _ 0 (by omega) (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  case h.refine_1 => rw [hM]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hsa
  case h.refine_2 =>
    rw [hM]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt (s.regs 30).isLt
  case h.refine_3 =>
    rw [hM]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
  case h.refine_4 => rw [hM]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hw
  all_goals (try (simp [setReg_apply, hM, h2]; done))
  all_goals (try (simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]; first | rfl | decide | (simp only [head, ip]; decide)))
  case h.refine_21 => intro k _ hk; omega
  case h.refine_22 =>
    intro s' hq
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hq
    refine ⟨q1, q2, q3, q4, ?_, ?_⟩
    · rw [q5, hM]
      exact (((Janus.MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 56, s.sp.toNat - 8)) (by simp)
        (by omega) (by omega)).writeLE _ (r := (s.sp.toNat - 56, s.sp.toNat - 8)) (by simp) (by omega) (by omega)).writeLE _
        (r := (s.sp.toNat + 8, s.sp.toNat + 16)) (by simp) (by omega) (by omega)
    · rcases q6 with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
      · exact Or.inl ⟨hall.mp a, by rw [b, hsum], c, d⟩
      · exact Or.inr ⟨fun h => a (hall.mpr h), b, c, d⟩
