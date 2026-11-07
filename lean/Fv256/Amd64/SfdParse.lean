import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.HexLemmas
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64

/-!
# `internal/strconv.ParseUint(s, 10, 64)` on a string of 1 to 19 bytes (amd64)

The digit loop of `strconv.ParseUint` for `base = 10`, `bitSize = 64`: for at most 19 bytes the value cannot overflow
(`10^19 - 1 < 2^64`), so the result is the number when every byte is an ASCII digit, and the internal syntax error
otherwise.  The error values are the addresses of the constant `internal/strconv.Error` objects in read-only data
(`ErrSyntax` is the constant at `dataAddr.«.rodata#9967e7a3»`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.I

namespace Fv256.Amd64.SfdParse

abbrev ip : Nat := segAddr Extracted.program "internal/strconv.ParseUint"
abbrev head : Nat := ip + 0x1b0

/-- the address of the `internal/strconv.ErrSyntax` constant (an `internal/strconv.Error`) -/
abbrev synAddr : Nat := Extracted.dataAddr.«.rodata#9967e7a3»
/-- the itab of `internal/strconv.Error` as an `error` -/
abbrev errItab : Nat := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»

def LoopQ (s : State) (M : Memory) (p len : Nat) (s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧ s'.mem = M ∧
  ((allDec (Fv256.C.bytesAt M p) 0 len ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 0 = 0 ∧ (s'.regs 3).toNat = errItab ∧ (s'.regs 1).toNat = synAddr))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem loop (impl : List Janus.Amd64.Segment) (s : State) (M : Memory) (p len : BitVec 64)
    (hL : 1 ≤ len.toNat) (hL2 : len.toNat ≤ 19)
    (hsa : M.accessible p.toNat len.toNat false = true) (hp : p.toNat + len.toNat ≤ 2 ^ 48)
    (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hlow : 0x20 ≤ (s.regs 4).toNat) (hnw : (s.regs 4).toNat + 16 ≤ 2 ^ 48)
    (hacc : M.accessible ((s.regs 4).toNat - 0x20) (0x20 + 16) true = true)
    (hrM : M.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (hbp : M.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) :
    ∀ n (S : State) (i : Nat), n = len.toNat - i → i ≤ len.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 1 = BitVec.ofNat 64 i → S.regs 6 = len →
      S.regs 10 = p → S.regs 11 = BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) →
      S.regs 2 = 0x199999999999999a#64 → S.regs 8 = 10#64 → S.regs 7 = 0xffffffffffffffff#64 →
      S.regs 0 = 10#64 → S.regs 12 = 0#64 → S.regs 4 = s.regs 4 - 0x20#64 → S.regs 5 = s.regs 4 - 8#64 →
      S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.df = s.df → S.fsBase = s.fsBase → S.mem = M →
      allDec (Fv256.C.bytesAt M p.toNat) 0 i →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S (LoopQ s M p.toNat len.toNat) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i hn hi hpc h1 h6 h10 h11 h2 h8 h7 h0 h12 h4 h5 h14 hx15 hdf hfs hmem hdig
    have hb256 : (Fv256.C.bytesAt M p.toNat i) < 256 ^ 1 := Janus.Arm64.Memory.readLE_lt M (p.toNat + i) 1
    have hdlt : decSum (Fv256.C.bytesAt M p.toNat) 0 i < 10 ^ i := decSum_lt _ 0 i (by simpa using hdig)
    have hd18 : i < len.toNat → decSum (Fv256.C.bytesAt M p.toNat) 0 i < 1000000000000000000 := fun h =>
      Nat.lt_of_lt_of_le hdlt (Nat.pow_le_pow_right (by decide) (by omega : i ≤ 18))
    have hy : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (M.readLE (p.toNat + i) 1)))) |||
        32#32).toNat < 256 := by
      rw [BitVec.toNat_or]
      have h1 : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (M.readLE (p.toNat + i) 1))))).toNat < 2 ^ 8 := by
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
      exact Nat.or_lt_two_pow (n := 8) h1 (by decide)
    have hcb0 : M.readLE (p.toNat + i) 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt M (p.toNat + i) 1
    have hm10 : i < len.toNat → (BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) * 10#64).toNat =
        decSum (Fv256.C.bytesAt M p.toNat) 0 i * 10 := by
      intro hlt
      have := hd18 hlt
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have h1 : decSum (Fv256.C.bytesAt M p.toNat) 0 i % 2 ^ 64 = decSum (Fv256.C.bytesAt M p.toNat) 0 i :=
        Nat.mod_eq_of_lt (by omega)
      rw [h1]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hlt : i < len.toNat
    all_goals (try have hm := hm10 hlt)
    all_goals (try have hd := hd18 hlt)
    all_goals janus64_run until [head]
    all_goals (try (exfalso; omega; done))
    all_goals (try (refine ih (len.toNat - (i + 1)) (by omega) _ (i + 1) rfl (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_))
    all_goals (try (simp [setRegF_apply, hmem, hdf, hx15, hfs, h14, h6, h10, h2, h8, h7, h0, h12, h4, h5]; done))
    all_goals (try (first | rfl | (simp only []; rfl) | decide))
    all_goals (try (unfold LoopQ))
    all_goals (try (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩))
    all_goals (try (simp [setRegF_apply, retAddrOf, hmem, hdf, hx15, hfs, h14, h6, h10, h2, h8, h7, h0, h12, h4, h5]; done))
    all_goals (try (case refine_18 => 
      (intro k hk hk'
       by_cases hki : k < i
       · exact hdig k hk hki
       · have hk2 : k = i := by omega
         subst hk2
         unfold isDec
         simp only [Fv256.C.bytesAt] at hb256 ⊢
         omega)))
    all_goals (try (case h.refine_5 =>
      (have hc : 48 ≤ M.readLE (p.toNat + i) 1 ∧ M.readLE (p.toNat + i) 1 ≤ 57 := by
         simp only [Fv256.C.bytesAt] at hb256
         omega
       simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
       rw [Fv256.I.step_val _ _ hc.1 hc.2]
       simp only [decSum, Fv256.C.bytesAt, Nat.zero_add])))
    all_goals (try (case hq.refine_9 =>
      first
      | (have hil : i = len.toNat := by omega
         subst hil
         left
         simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
         refine ⟨hdig, ?_, rfl, rfl⟩
         have h10 : 10 ^ len.toNat ≤ 10 ^ 19 := Nat.pow_le_pow_right (by decide) hL2
         rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      | (right
         simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
         refine ⟨?_, ?_, ?_, ?_⟩
         · intro hall
           have h := hall i (by omega) (by omega)
           simp only [Fv256.C.bytesAt, isDec] at h
           have hcb : M.readLE (p.toNat + i) 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt M (p.toNat + i) 1
           have hD64 : decSum (Fv256.C.bytesAt M p.toNat) 0 i < 18446744073709551616 :=
             Nat.lt_of_lt_of_le hdlt (Nat.le_trans (Nat.pow_le_pow_right (by decide) hi |> fun h => Nat.le_trans h (Nat.pow_le_pow_right (by decide) hL2)) (by decide))
           clear ih hmem hpc h1 h6 h10 h11 h2 h8 h7 h0 h12 h4 h5 h14 hx15 hdf hfs hdig hsa hacc hrM hbp hret hy hdlt hb256 hall
           generalize M.readLE (p.toNat + i) 1 = c at *
           generalize decSum (Fv256.C.bytesAt M p.toNat) 0 i = D at *
           simp only [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
             BitVec.toNat_or, BitVec.toNat_mul, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod] at *
           try rw [Nat.mod_eq_of_lt hD64] at *
           omega
         · first | rfl | decide
         · first | rfl | decide
         · first | rfl | decide)))
    all_goals (try (
      exfalso
      have hD64 : decSum (Fv256.C.bytesAt M p.toNat) 0 i < 18446744073709551616 :=
        Nat.lt_of_lt_of_le hdlt (Nat.le_trans (Nat.pow_le_pow_right (by decide) hi |> fun h => Nat.le_trans h (Nat.pow_le_pow_right (by decide) hL2)) (by decide))
      have hcb : M.readLE (p.toNat + i) 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt M (p.toNat + i) 1
      clear ih hmem hpc h1 h6 h10 h11 h2 h8 h7 h0 h12 h4 h5 h14 hx15 hdf hfs hdig hsa hacc hrM hbp hret hy hdlt hb256
      generalize M.readLE (p.toNat + i) 1 = c at *
      generalize decSum (Fv256.C.bytesAt M p.toNat) 0 i = D at *
      simp only [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        BitVec.toNat_or, BitVec.toNat_mul, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod] at *
      try rw [Nat.mod_eq_of_lt hD64] at *
      omega
      done))


theorem rr_mono {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

def PuPre (p len : BitVec 64) (s : State) : Prop :=
  Fv256.C.RetOK s ∧ s.regs 0 = p ∧ s.regs 3 = len ∧ s.regs 1 = 10#64 ∧ s.regs 7 = 64#64 ∧
  Buffer s p len.toNat false ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 19 ∧ StackGuardOK s 0 ∧ StackWritable s 0x20 16 ∧
  (p.toNat + len.toNat ≤ (s.regs 4).toNat - 0x20 ∨ (s.regs 4).toNat + 16 ≤ p.toNat)

def PuPost (p len : BitVec 64) (s s' : State) : Prop :=
  Fv256.C.Kept s s' ∧
  MemFrame s.mem s'.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] ∧
  ((allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧
      (s'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 0 = 0 ∧ (s'.regs 3).toNat = errItab ∧
      (s'.regs 1).toNat = synAddr))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem pu_sum (impl : List Janus.Amd64.Segment) (p len : BitVec 64) :
    Summary (Extracted.program.link impl) ip (PuPre p len) (PuPost p len) := by
  intro s hpc ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, ⟨hpw, hp⟩, hL, hL2, hg, ⟨hlow, hnw, hacc⟩, hdisj⟩
  simp only [regSP] at hacc hlow hnw hdisj
  have hgl := hg.load
  have hgb := hg.below
  have hgn := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hgn hgr
  janus64_run until [head]
  obtain ⟨M, hM⟩ : ∃ M, M = (Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 8) 8 p.toNat := ⟨_, rfl⟩
  rw [← hM]
  have hbytes : ∀ k, k < len.toNat → Fv256.C.bytesAt M p.toNat k = Fv256.C.bytesAt s.mem p.toNat k := by
    intro k hk
    simp only [hM, Fv256.C.bytesAt]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hsum : decSum (Fv256.C.bytesAt M p.toNat) 0 len.toNat = decSum (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat :=
    decSum_congr _ _ 0 _ (fun k _ hk => hbytes k (by omega))
  have hall : allDec (Fv256.C.bytesAt M p.toNat) 0 len.toNat ↔ allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat :=
    ⟨fun h k a b => by rw [← hbytes k (by omega)]; exact h k a b, fun h k a b => by rw [hbytes k (by omega)]; exact h k a b⟩
  refine rr_mono (loop impl s M p len hL hL2 ?_ hpw hra2 hlow hnw ?_ ?_ ?_ (len.toNat - 0) _ 0 rfl (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_
  case h.refine_1 => rw [hM]; simpa using hp
  case h.refine_2 => rw [hM]; simpa using hacc
  case h.refine_3 =>
    rw [hM]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  case h.refine_4 =>
    rw [hM]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt (s.regs 5).isLt
  case h.refine_22 => intro k _ hk; omega
  all_goals (try (simp [setRegF_apply, hM, retAddrOf, hdf, hx15]; done))
  case h.refine_5 =>
    simp only [setRegF_apply]
    first | rfl | decide | (simp only [head, ip]; decide)
  case h.refine_9 =>
    simp only [setRegF_apply, decSum]
    rfl
  case h.refine_23 =>
    intro s' hq
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hq
    refine ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, ?_, ?_⟩
    · rw [h8, hM]
      exact (((Janus.MemFrame.refl s.mem _).writeLE _ (r := ((s.regs 4).toNat - 8, (s.regs 4).toNat)) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16))
        (by simp) (by dsimp only; omega) (by dsimp only; omega))
    · rw [hall.symm.trans (Iff.refl _)] at *
      rcases h9 with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
      · exact Or.inl ⟨hall.mp a, by rw [b, hsum], c, d⟩
      · exact Or.inr ⟨fun h => a (hall.mpr h), b, c, d⟩

end Fv256.Amd64.SfdParse
