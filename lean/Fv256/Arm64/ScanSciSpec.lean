import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.DecCongr
import Fv256.IndexByteSpec
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.SpecF
import Fv256.UtilSa
import Fv256.Arm64.MulOverflowProg

/-!
# `scanScientificFromString` (arm64): precondition, postcondition and the `SetFromDecimal` call-site transfer (Extracted-free)

`SciPre`: the precondition of `SetFromDecimal(dst, s)` (`TopPre`) plus room for `scanScientificFromString`'s frame (112 bytes) and
the overread assumption of `IndexByteString`.
`SciPost`: the documented result `ScanSpec.sciParse`.
`toppre_sub`: `TopPre` for a `SetFromDecimal` call made from inside `scanScientificFromString`, on a (possibly smaller) window,
a destination that is either `dst` or a local `Int` inside the window, and a sub-slice of the string.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.ScanSciSpec

variable (C : SfdCfg)

/-- precondition of `scanScientificFromString(dst, s)`: `dst` in `X0`, `s.ptr` in `X1`, `s.len` in `X2` -/
def SciPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) : Prop :=
  TopPre C R R2 T b L lo hi dst pS nS s ∧ lo + 4640 ≤ s.sp.toNat ∧
    Fv256.IndexByte.PageReadable s.mem pS.toNat nS.toNat

/-- the documented result of `scanScientificFromString` (the value of `dst` on an error return is unspecified) -/
def SciPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst pS nS : BitVec 64)
    (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  s'.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ s'.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 ∧
  ((∃ v, Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = v ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE C.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (C.ioEOF + 8) 8 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
      (s'.regs 0).toNat = s.mem.readLE C.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (C.errBig + 8) 8 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (∃ lo' len', Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 C.numErrItab ∧ s'.regs 1 = t ∧
        TeObj C R b L (BitVec.ofNat 64 C.fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])))

/-- (copy of `FromDecimalSpec.chunkOK_mono`, which is tied to the old window bound) -/
theorem chunkOK_mono {R : RtInv} {R2 : IfaceModel} {L L' : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64} {lo hi hi3 : Nat}
    {m m' : Janus.Arm64.Memory} (h : ChunkOK C R R2 L b sp sl lo hi m) (hL : ∀ r ∈ L, r ∈ L') (hh : hi3 ≤ hi)
    (hacc : m'.accessible sp.toNat sl.toNat false = true) : ChunkOK C R R2 L' b sp sl lo hi3 m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, hacc, h5, by omega, h7.elim Or.inl (fun hi => Or.inr (hi.of_subset hL)), h8⟩

/-- package-initialisation facts about the sentinel errors (as `FromDecimalSpec.InitDone`) -/
def InitDone (R2 : IfaceModel) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE C.ioEOF 8 ≠ 0 ∧ m.readLE (C.ioEOF + 8) 8 ≠ 0 ∧ m.readLE C.errBig 8 ≠ 0 ∧ m.readLE (C.errBig + 8) 8 ≠ 0 ∧
  (∀ r ∈ R2.priv, r.1 ≤ r.2)

theorem outside_win {a n lo hi hi' z z' : Nat} (h : Outside a n [(lo, hi), (z, z + 32)]) (hhi : hi' ≤ hi)
    (hz : z' = z ∨ (lo ≤ z' ∧ z' + 32 ≤ hi)) : Outside a n [(lo, hi'), (z', z' + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢
  omega

/-- `TopPre` for a `SetFromDecimal` call inside `scanScientificFromString`.

`s0` is the state at the entry of `scanScientificFromString` (`TopPre` for `dst`, `pS`, `nS` on the window `[lo, hi)`), `S` the state
at the call: its memory differs from `s0`'s only inside `[lo, hi)` and `[dst, dst+32)` (`hF`), and the runtime environment holds in `S`
for the smaller window `[lo, hi')` (`hEnv`).  The call's destination `z'` is `dst` or a 32-byte local inside `[lo, hi)` above `hi'`, its
string `(pS', nS')` a sub-slice of `(pS, nS)`. -/
theorem toppre_sub {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {z pS nS z' pS' nS' : BitVec 64} {s0 S : State}
    (hpre : TopPre C R R2 T b L lo hi z pS nS s0)
    (hEnv : Env C R R2 T b L lo hi' S)
    (hF : MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)])
    (hhi' : hi' ≤ hi)
    (hz'in : z'.toNat = z.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ hi)) (hz'win : z'.toNat + 32 ≤ lo ∨ hi' ≤ z'.toNat)
    (hsub : nS'.toNat = 0 ∨ (pS.toNat ≤ pS'.toNat ∧ pS'.toNat + nS'.toNat ≤ pS.toNat + nS.toNat))
    (hP48' : pS'.toNat + nS'.toNat ≤ 2 ^ 48)
    (hr0 : S.regs 0 = z') (hr1 : S.regs 1 = pS') (hr2 : S.regs 2 = nS')
    (h30a : (S.regs 30).toNat % 4 = 0) (h30b : (S.regs 30).toNat < 2 ^ 48)
    (hr28 : S.regs 28 = s0.regs 28)
    (hlo : lo + 4528 ≤ S.sp.toNat) (hhi : S.sp.toNat + 32 ≤ hi')
    (hz'R : Outside z'.toNat 32 R.rt ∨ InRanges z'.toNat 32 L) (hz'P : Outside z'.toNat 32 R2.priv)
    (hz'S : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z'.toNat, z'.toNat + 32)])
    (hz'g : (s0.regs 28).toNat + 16 + 8 ≤ z'.toNat ∨ z'.toNat + 32 ≤ (s0.regs 28).toNat + 16)
    (hz'acc : S.mem.accessible z'.toNat 32 true = true) (hz'48 : z'.toNat + 32 ≤ 2 ^ 48) :
    TopPre C R R2 T b L lo hi' z' pS' nS' S := by
  obtain ⟨-, -, -, -, -, hMod, hEnv0, hlo0, hhi0, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS, hzg,
    hPA, hP48, hPW, hPZ, hCh⟩ := hpre
  have hrt : ∀ a n, Outside a n [(lo, hi), (z.toNat, z.toNat + 32)] → S.mem.readLE a n = s0.mem.readLE a n :=
    fun a n h => hF.readLE a n h
  have hz' : z'.toNat = z.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ hi) := hz'in
  have hw := fun {a n : Nat} (h : Outside a n [(lo, hi), (z.toNat, z.toNat + 32)]) => outside_win (hi' := hi') (z' := z'.toNat) h hhi' hz'
  unfold TopPre
  refine ⟨h30a, h30b, hr0, hr1, hr2, hMod, hEnv, hlo, hhi, ?_, ?_, ?_, ?_, ?_, hMr, ?_, ?_, ?_, ?_, hz'win, hz'R, hz'P, hz'S,
    (by rw [hr28]; exact hz'g), ?_, hP48', ?_, ?_, ?_⟩
  · -- MultOK
    obtain ⟨u1, u2, u3⟩ := hMult
    refine ⟨by rw [hF.accessible]; exact u1, hw u2, ?_⟩
    intro k hk1 hk2
    obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
    have hread : S.mem.readLE (C.mulTab + 8 * k) 8 = s0.mem.readLE (C.mulTab + 8 * k) 8 := by
      refine hrt _ _ (Outside.of_sub u2 (by omega) (by omega))
    rw [hread]
    have v4' := v4
    simp only [outside_cons, outside_nil, and_true] at v4'
    generalize s0.mem.readLE (C.mulTab + 8 * k) 8 = pp at *
    refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, hw v4⟩
    have hv : S.mem.readLE pp 32 = s0.mem.readLE pp 32 := hrt pp 32 (by
      simp only [outside_cons, outside_nil, and_true]; exact v4')
    show S.mem.readLE pp 32 = _
    rw [hv]; exact v3
  · rw [hF.accessible]; exact hE1
  · exact hw hE2
  · rw [hF.accessible]; exact hMa
  · exact hw hMo
  · intro k hk
    rw [hrt _ _ (Outside.of_sub hMo (by omega) (by omega))]
    exact hMb k hk
  · rw [hF.accessible]; exact hB1
  · exact hw hB2
  · exact ⟨hz'acc, hz'48⟩
  · -- string facts
    rcases hsub with h | h
    · exact Or.inl h
    · rcases hPA with h1 | h1
      · exact Or.inl (by omega)
      · exact Or.inr (by rw [hF.accessible]; exact Janus.Arm64.Memory.accessible_sub _ h1 (Or.inl rfl) h.1 (by omega))
  · rcases hsub with h | h
    · exact Or.inl h
    · rcases hPW with h1 | h1 | h1
      · omega
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
  · rcases hsub with h | h
    · exact Or.inl h
    · rcases hz' with h2 | h2
      · rcases hPZ with h1 | h1 | h1
        · omega
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
      · rcases hPW with h1 | h1 | h1
        · omega
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))
  · intro sp sl h1 h2 h3 h4
    have h5 : pS.toNat ≤ sp ∧ sp + sl ≤ pS.toNat + nS.toNat := by
      rcases hsub with h | h <;> omega
    have := hCh sp sl h5.1 h5.2 h3 h4
    refine chunkOK_mono C this (fun r hr => hr) hhi' ?_
    rw [hF.accessible]; exact this.2.2.2.1

/-- `toppre_sub` for the state `Sx` (any state whose memory is a frame of the entry memory and whose `SP` is in the window):
the runtime environment is derived from the entry one. -/
theorem call_pre {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {z pS nS z' pS' nS' : BitVec 64} {s0 Sx : State}
    (hpre : TopPre C R R2 T b L lo hi z pS nS s0)
    (hF : MemFrame s0.mem Sx.mem [(lo, hi), (z.toNat, z.toNat + 32)])
    (hal : Sx.sp.toNat % 16 = 0) (hhi' : hi' ≤ hi)
    (hz'in : z'.toNat = z.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ hi)) (hz'win : z'.toNat + 32 ≤ lo ∨ hi' ≤ z'.toNat)
    (hsub : nS'.toNat = 0 ∨ (pS.toNat ≤ pS'.toNat ∧ pS'.toNat + nS'.toNat ≤ pS.toNat + nS.toNat))
    (hP48' : pS'.toNat + nS'.toNat ≤ 2 ^ 48)
    (hr0 : Sx.regs 0 = z') (hr1 : Sx.regs 1 = pS') (hr2 : Sx.regs 2 = nS')
    (h30a : (Sx.regs 30).toNat % 4 = 0) (h30b : (Sx.regs 30).toNat < 2 ^ 48)
    (hr28 : Sx.regs 28 = s0.regs 28)
    (hlo : lo + 4528 ≤ Sx.sp.toNat) (hhi : Sx.sp.toNat + 32 ≤ hi')
    (hz'R : Outside z'.toNat 32 R.rt ∨ InRanges z'.toNat 32 L) (hz'P : Outside z'.toNat 32 R2.priv)
    (hz'S : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z'.toNat, z'.toNat + 32)])
    (hz'g : (s0.regs 28).toNat + 16 + 8 ≤ z'.toNat ∨ z'.toNat + 32 ≤ (s0.regs 28).toNat + 16)
    (hz'acc : Sx.mem.accessible z'.toNat 32 true = true) (hz'48 : z'.toNat + 32 ≤ 2 ^ 48) :
    TopPre C R R2 T b L lo hi' z' pS' nS' Sx := by
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, hMod, hEnv, -, -, -, -, -, -, -, -, -, -, -, -, -, hzR, hzPr, hzS, hzg, -⟩ := hpre'
  have hEnv' := hEnv
  obtain ⟨e1, e2, -⟩ := hEnv'
  have e1' := Env.frame (C := C) hMod.1 hEnv (s' := Sx) ⟨by omega, by omega, hal⟩ hr28 hF hzR hzPr hzS hzg
  exact toppre_sub C hpre (Env.shrink e1' (Nat.le_refl _) hhi' (by omega) (by omega)) hF hhi' hz'in hz'win hsub hP48' hr0 hr1 hr2 h30a h30b
    hr28 hlo hhi hz'R hz'P hz'S hz'g hz'acc hz'48

theorem out_ok {a n lo hi sp dst S : Nat} (h : Outside a n [(lo, hi), (dst, dst + 32)]) (hl : lo ≤ sp) (h1 : sp + 32 ≤ hi) (hS : S + 112 = sp) :
    Outside a n [(lo, S + 32), (dst, dst + 32)] ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

theorem out_syn {a n lo hi sp dst S : Nat} {rs : List (Nat × Nat)}
    (h : Outside a n (rs ++ [(lo, hi), (dst, dst + 32)])) (hl : lo ≤ sp) (h1 : sp + 32 ≤ hi) (hS : S + 112 = sp) :
    Outside a n (rs ++ [(lo, S + 32), (dst, dst + 32)]) ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h0, h2, h3⟩ := h
  refine ⟨⟨h0, ?_, h3⟩, ?_⟩ <;> omega

theorem out_win {a n lo hi sp dst : Nat} (h : Outside a n [(lo, hi), (dst, dst + 32)]) (hl : lo ≤ sp) (h1 : sp + 32 ≤ hi) :
    Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢; omega

/-! ## `sciParse` lemmas -/

theorem find_congr {α : Type} (p q : α → Bool) : ∀ l : List α, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.find?_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem idxE_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) :
    Fv256.ScanSpec.idxE b n = Fv256.ScanSpec.idxE b' n := by
  unfold Fv256.ScanSpec.idxE
  exact find_congr _ _ _ (fun x hx => by
    have := h x (List.mem_range.1 hx)
    simp only [this])

theorem sciParse_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) :
    Fv256.ScanSpec.sciParse b n = Fv256.ScanSpec.sciParse b' n := by
  unfold Fv256.ScanSpec.sciParse
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    rw [idxE_congr b b' n h]
    cases hi : Fv256.ScanSpec.idxE b' n with
    | none => exact Fv256.I.decParse_congr b b' n h
    | some i =>
      have hi' : i < n := List.mem_range.1 (List.mem_of_find?_eq_some hi)
      simp only
      rw [Fv256.I.decParse_congr b b' i (fun k hk => h k (by omega))]
      have hc : (n - (i + 1) = 1 ∧ b (i + 1) = 48) ↔ (n - (i + 1) = 1 ∧ b' (i + 1) = 48) := by
        by_cases h1 : n - (i + 1) = 1
        · rw [h (i + 1) (by omega)]
        · simp [h1]
      have hd : Fv256.I.decParse (fun k => b (i + 1 + k)) (n - (i + 1)) =
          Fv256.I.decParse (fun k => b' (i + 1 + k)) (n - (i + 1)) :=
        Fv256.I.decParse_congr _ _ _ (fun k hk => h (i + 1 + k) (by omega))
      rw [hd]
      simp only [hc]

theorem indexOf_eq_idxE (b : Nat → Nat) (n : Nat) :
    Fv256.IndexByte.indexOfNat b n 101 = (match Fv256.ScanSpec.idxE b n with | some i => i | none => 2 ^ 64 - 1) := by
  unfold Fv256.IndexByte.indexOfNat Fv256.ScanSpec.idxE
  rfl

theorem idxE_some {b : Nat → Nat} {n i : Nat} (h : Fv256.ScanSpec.idxE b n = some i) :
    i < n ∧ b i = 101 ∧ ∀ j, j < i → b j ≠ 101 := by
  unfold Fv256.ScanSpec.idxE at h
  refine ⟨List.mem_range.1 (List.mem_of_find?_eq_some h), ?_, ?_⟩
  · have := List.find?_some h
    simpa using this
  · intro j hj hj'
    have := List.find?_eq_some_iff_getElem.1 h
    obtain ⟨_, k, hk, hk2, hk3⟩ := this
    have e : i = k := by rw [← hk2]; simp
    subst e
    have := hk3 j hj
    simp [hj'] at this

section cases
open Fv256.ScanSpec

theorem sci_zero (b : Nat → Nat) : sciParse b 0 = Res.ok 0 := by
  unfold sciParse; simp

theorem sci_none {b : Nat → Nat} {n : Nat} (hn : n ≠ 0) (h : idxE b n = none) : sciParse b n = decParse b n := by
  unfold sciParse; simp [hn, h]

theorem sci_mant_eof {b : Nat → Nat} {n i : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.eof) :
    sciParse b n = Res.eof := by
  unfold sciParse; simp [hn, h, hr]

theorem sci_mant_range {b : Nat → Nat} {n i : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.range) :
    sciParse b n = Res.range := by
  unfold sciParse; simp [hn, h, hr]

theorem sci_mant_syn {b : Nat → Nat} {n i lo len : Nat} (hn : n ≠ 0) (h : idxE b n = some i)
    (hr : decParse b i = Res.syntax lo len) : sciParse b n = Res.syntax lo len := by
  unfold sciParse; simp [hn, h, hr]

theorem sci_e0 {b : Nat → Nat} {n i v : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.ok v)
    (h1 : n - (i + 1) = 1) (h2 : b (i + 1) = 48) : sciParse b n = Res.ok v := by
  unfold sciParse; simp [hn, h, hr, h1, h2]
  rfl

theorem sci_exp_ok {b : Nat → Nat} {n i v e : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.ok v)
    (h0 : ¬ (n - (i + 1) = 1 ∧ b (i + 1) = 48)) (he : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = Res.ok e) :
    sciParse b n = (if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Res.range else Res.ok (v * 10 ^ e)) := by
  unfold sciParse; simp only [hn, ite_false, h, hr, h0, he]
  rfl

theorem sci_exp_eof {b : Nat → Nat} {n i v : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.ok v)
    (h0 : ¬ (n - (i + 1) = 1 ∧ b (i + 1) = 48)) (he : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = Res.eof) :
    sciParse b n = Res.eof := by
  unfold sciParse; simp only [hn, ite_false, h, hr, h0, he]
  rfl

theorem sci_exp_range {b : Nat → Nat} {n i v : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.ok v)
    (h0 : ¬ (n - (i + 1) = 1 ∧ b (i + 1) = 48)) (he : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = Res.range) :
    sciParse b n = Res.range := by
  unfold sciParse; simp only [hn, ite_false, h, hr, h0, he]
  rfl

theorem sci_exp_syn {b : Nat → Nat} {n i v lo len : Nat} (hn : n ≠ 0) (h : idxE b n = some i) (hr : decParse b i = Res.ok v)
    (h0 : ¬ (n - (i + 1) = 1 ∧ b (i + 1) = 48)) (he : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = Res.syntax lo len) :
    sciParse b n = Res.syntax (i + 1 + lo) len := by
  unfold sciParse; simp only [hn, ite_false, h, hr, h0, he]
  rfl

end cases

theorem teobj_xfer {R : RtInv} {b : Nat} {L : List (Nat × Nat)} {fp fl sp sl : BitVec 64} {s S S3 Sf : State} {q t : Nat}
    (hr28 : S.regs 28 = s.regs 28) (hSm : Sf.mem = S3.mem)
    (h1 : S.mem.readLE C.strconvErrSyntax 8 = s.mem.readLE C.strconvErrSyntax 8)
    (h2 : S.mem.readLE (C.strconvErrSyntax + 8) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8)
    (h3 : ∀ k, k < sl.toNat → S.mem.readLE (sp.toNat + k) 1 = s.mem.readLE (sp.toNat + k) 1)
    (h : TeObj C R b L fp fl sp sl S S3 q t) : TeObj C R b L fp fl sp sl s Sf q t := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  unfold TeObj
  rw [hSm]
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, ?_, ?_, ?_, ?_⟩
  · rw [a9, h1]
  · rw [a10, h2]
  · intro k hk; rw [a11 k hk, h3 k hk]
  · rw [← hr28]; exact a12

theorem out_two {a n lo hi sp dst : Nat} (h : Outside a n [(lo, hi), (dst, dst + 32)]) (hl : lo ≤ sp) (h1 : sp + 32 ≤ hi) :
    Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := out_win h hl h1

theorem out_syn8 {a n lo sp dst S : Nat} {rs : List (Nat × Nat)}
    (h : Outside a n (rs ++ [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)])) (hS : S + 112 = sp) :
    Outside a n (rs ++ [(lo, S + 32), (dst, dst + 32)]) ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h0, h2, h3, h4⟩ := h
  refine ⟨⟨h0, ?_, h4⟩, h2, h3, h4⟩ <;> omega
/-- what every state `S` of the body after the prologue satisfies, relative to the entry state `s0` -/
def Fr (lo : Nat) (dst pS nS : BitVec 64) (s0 S : State) : Prop :=
  S.sp = s0.sp - 112#64 ∧ S.regs 28 = s0.regs 28 ∧ S.regs 18 = s0.regs 18 ∧ S.regs 29 = s0.sp - 120#64 ∧
  MemFrame s0.mem S.mem [(lo, s0.sp.toNat - 8), (s0.sp.toNat + 8, s0.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] ∧
  S.mem.regions = s0.mem.regions ∧
  S.mem.readLE (s0.sp.toNat - 112) 8 = (s0.regs 30).toNat ∧ S.mem.readLE (s0.sp.toNat - 120) 8 = (s0.regs 29).toNat ∧
  S.mem.readLE (s0.sp.toNat + 8) 8 = dst.toNat ∧ S.mem.readLE (s0.sp.toNat + 16) 8 = pS.toNat ∧
  S.mem.readLE (s0.sp.toNat + 24) 8 = nS.toNat

theorem str_outside {pS nS lo hi dst sp : Nat} (hPW : nS = 0 ∨ pS + nS ≤ lo ∨ hi ≤ pS)
    (hPZ : nS = 0 ∨ pS + nS ≤ dst ∨ dst + 32 ≤ pS) (hlo : lo ≤ sp) (hhi : sp + 32 ≤ hi) (k : Nat) (hk : k < nS) :
    Outside (pS + k) 1 [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true]; omega


theorem out_gen {a n lo hi hi' sp dst z' : Nat} (h : Outside a n [(lo, hi), (dst, dst + 32)]) (hhi' : hi' ≤ sp - 8)
    (hl : lo ≤ sp) (h1 : sp + 32 ≤ hi) (hz' : z' = dst ∨ (lo ≤ z' ∧ z' + 32 ≤ sp - 8)) :
    Outside a n [(lo, hi'), (z', z' + 32)] ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at h ⊢
  omega

theorem out_gen2 {a n lo hi' sp dst z' : Nat} (h : Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)])
    (hhi' : hi' ≤ sp - 8) (hz' : z' = dst ∨ (lo ≤ z' ∧ z' + 32 ≤ sp - 8)) :
    Outside a n [(lo, hi'), (z', z' + 32)] ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  refine ⟨?_, h⟩
  simp only [outside_cons, outside_nil, and_true] at h ⊢
  omega

theorem out_gen3 {a n lo hi' sp dst z' : Nat} {rs : List (Nat × Nat)}
    (h : Outside a n (rs ++ [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)]))
    (hhi' : hi' ≤ sp - 8) (hz' : z' = dst ∨ (lo ≤ z' ∧ z' + 32 ≤ sp - 8)) :
    Outside a n (rs ++ [(lo, hi'), (z', z' + 32)]) ∧ Outside a n [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h0, h2, h3, h4⟩ := h
  refine ⟨⟨h0, ?_⟩, h2, h3, h4⟩
  omega

theorem out_sp8 {lo hi sp dst : Nat} (hz : dst + 32 ≤ lo ∨ hi ≤ dst) (hl : lo + 8 ≤ sp) (hh : sp + 32 ≤ hi) :
    Outside (sp - 8) 8 [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_sp0 {lo hi sp dst : Nat} (hz : dst + 32 ≤ lo ∨ hi ≤ dst) (hl : lo + 8 ≤ sp) (hh : sp + 32 ≤ hi) :
    Outside sp 8 [(lo, sp - 8), (sp + 8, sp + 32), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem out_two_of {a n lo hi dst : Nat} (h1 : Outside a n [(lo, hi)]) (h2 : Outside a n [(dst, dst + 32)]) :
    Outside a n [(lo, hi), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true] at *; exact ⟨h1, h2⟩

theorem fr_hSs {lo : Nat} {dst pS nS : BitVec 64} {s S : State} (hfr : Fr lo dst pS nS s S) : S.sp.toNat + 112 = s.sp.toNat ∨ s.sp.toNat < 112 := by
  obtain ⟨fsp, -⟩ := hfr
  rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem bytes_xfer {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {dst pS nS : BitVec 64}
    {s S : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hfr : Fr lo dst pS nS s S) :
    ∀ k, k < nS.toNat → S.mem.readLE (pS.toNat + k) 1 = s.mem.readLE (pS.toNat + k) 1 := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  exact fun k hk => (fmf.readLE (pS.toNat + k) 1 (str_outside hPW hPZ (by omega) hhi k hk))

theorem post_syn {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' off lo' len' : Nat}
    {dst pS nS z' pS' nS' t : BitVec 64} {q : Nat} {s S S3 Sf : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (hz' : z'.toNat = dst.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ s.sp.toNat - 8))
    (hsub : pS'.toNat = pS.toNat + off ∧ off + nS'.toNat ≤ nS.toNat)
    (hv : decParse (bytesAt s.mem pS'.toNat) nS'.toNat = .syntax lo' len')
    (c0 : S3.regs 0 = BitVec.ofNat 64 C.numErrItab) (c1 : S3.regs 1 = t)
    (cTe : TeObj C R b L (BitVec.ofNat 64 C.fnStr) 9#64 (BitVec.ofNat 64 (pS'.toNat + lo')) (BitVec.ofNat 64 len') S S3 q t.toNat)
    (cMF : MemFrame S.mem S3.mem (R.rt ++ R2.priv ++ [(lo, hi'), (z'.toNat, z'.toNat + 32)]))
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hS0 : Sf.regs 0 = S3.regs 0) (hS1 : Sf.regs 1 = S3.regs 1) (hSm : Sf.mem = S3.mem)
    (hsyn : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax (off + lo') len') :
    SciPost C R R2 T b L lo hi dst pS nS s Sf := by
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, -⟩ := hEnv
  have hbS := bytes_xfer C htop hfr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  have hSs : S.sp.toNat + 112 = s.sp.toNat := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hlift : ∀ (rs : List (Nat × Nat)) (ws1 : List (Nat × Nat)), MemFrame S.mem S3.mem ws1 →
      (∀ a n, Outside a n rs → Outside a n ws1 ∧ Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) →
      MemFrame s.mem S3.mem rs := fun rs ws1 h2 hout => fmf.trans h2 (fun a n ho => by
        have := hout a n ho; exact ⟨this.2, this.1⟩)
  have hI0 : ∀ (a n : Nat), Outside a n [(lo, hi), (dst.toNat, dst.toNat + 32)] →
      Outside a n [(lo, hi'), (z'.toNat, z'.toNat + 32)] ∧
      Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] :=
    fun a n h => out_gen h hhi' (Nat.le_trans (by omega) hlo) hhi hz'
  have hM3 := hlift (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) _ cMF
    (fun a n h => by
      simp only [outside_append] at h
      have := hI0 a n h.2
      refine ⟨?_, this.2⟩
      simp only [outside_append]; exact ⟨h.1, this.1⟩)
  have hM8 := hlift (R.rt ++ R2.priv ++ [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) _ cMF
    (fun a n h => out_gen3 h hhi' hz')
  have hsyn2 := Fv256.I.decParse_syntax _ _ _ _ hv
  have hWs : Outside C.strconvErrSyntax 16 [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    out_two_of (by simpa using hr14 (C.strconvErrSyntax, C.strconvErrSyntax + 16) (by simp [staticRanges]))
      (by simpa using hzS (C.strconvErrSyntax, C.strconvErrSyntax + 16) (by simp [staticRanges]))
  have hWs' := (hI0 _ _ hWs).2
  have hRT8 : ∀ a n, lo ≤ a → a + n ≤ hi → Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] →
      Outside a n (R.rt ++ R2.priv ++ [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) := by
    intro a n h1 h2 h3
    simp only [outside_append]
    exact ⟨⟨Outside.of_sub hr9 h1 (by omega), Outside.of_sub hr10 h1 (by omega)⟩, h3⟩
  unfold SciPost
  rw [hSm]
  refine ⟨hSsp, hS29, hS28, hS18, hM8.readLE _ _ (hRT8 _ _ (by omega) (by omega) (out_sp8 hzW (by omega) hhi)),
    hM8.readLE _ _ (hRT8 _ _ (by omega) (by omega) (out_sp0 hzW (by omega) hhi)),
    Or.inr (Or.inr (Or.inr ⟨off + lo', len', hsyn, q, t, ?_, ?_, ?_, hM3⟩))⟩
  · rw [hS0]; exact c0
  · rw [hS1]; exact c1
  · have e1 : BitVec.ofNat 64 (pS.toNat + (off + lo')) = BitVec.ofNat 64 (pS'.toNat + lo') := by
      rw [hsub.1]; congr 1; omega
    rw [e1]
    have g1 : S.mem.readLE C.strconvErrSyntax 8 = s.mem.readLE C.strconvErrSyntax 8 :=
      fmf.readLE _ _ (Outside.of_sub hWs' (Nat.le_refl _) (by omega))
    have g2 : S.mem.readLE (C.strconvErrSyntax + 8) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8 :=
      fmf.readLE _ _ (Outside.of_sub hWs' (by omega) (by omega))
    have g3 : ∀ k, k < (BitVec.ofNat 64 len').toNat → S.mem.readLE ((BitVec.ofNat 64 (pS'.toNat + lo')).toNat + k) 1 =
        s.mem.readLE ((BitVec.ofNat 64 (pS'.toNat + lo')).toNat + k) 1 := by
      intro k hk
      simp only [BitVec.toNat_ofNat] at hk ⊢
      rw [Nat.mod_eq_of_lt (show pS'.toNat + lo' < 2 ^ 64 by omega)]
      have := hbS (off + lo' + k) (by omega)
      rw [show pS'.toNat + lo' + k = pS.toNat + (off + lo' + k) by omega]; exact this
    exact teobj_xfer C f28 hSm g1 g2 g3 cTe

/-- common set-up for the post-call lemmas -/
theorem lift_frame {lo : Nat} {dst : BitVec 64} {s S S3 : State} {ws1 : List (Nat × Nat)} (rs : List (Nat × Nat))
    (fmf : MemFrame s.mem S.mem [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)])
    (h2 : MemFrame S.mem S3.mem ws1)
    (hout : ∀ a n, Outside a n rs → Outside a n ws1 ∧ Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) :
    MemFrame s.mem S3.mem rs := fmf.trans h2 (fun a n ho => by
        have := hout a n ho; exact ⟨this.2, this.1⟩)

theorem post_eor {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {dst pS nS z' : BitVec 64} {s S S3 Sf : State} {a0 : Nat}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (hz' : z'.toNat = dst.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ s.sp.toNat - 8))
    (hA : Outside a0 16 [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (c0 : (S3.regs 0).toNat = S.mem.readLE a0 8) (c1 : (S3.regs 1).toNat = S.mem.readLE (a0 + 8) 8)
    (cMF : MemFrame S.mem S3.mem [(lo, hi'), (z'.toNat, z'.toNat + 32)])
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hS0 : Sf.regs 0 = S3.regs 0) (hS1 : Sf.regs 1 = S3.regs 1) (hSm : Sf.mem = S3.mem) :
    Sf.sp = s.sp ∧ Sf.regs 29 = s.regs 29 ∧ Sf.regs 28 = s.regs 28 ∧ Sf.regs 18 = s.regs 18 ∧
    Sf.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ Sf.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 ∧
    (Sf.regs 0).toNat = s.mem.readLE a0 8 ∧ (Sf.regs 1).toNat = s.mem.readLE (a0 + 8) 8 ∧
    MemFrame s.mem Sf.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] := by
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  have hlh : lo ≤ s.sp.toNat := Nat.le_trans (by omega) hlo
  have hM3 := lift_frame [(lo, hi), (dst.toNat, dst.toNat + 32)] fmf cMF (fun a n h => out_gen h hhi' hlh hhi hz')
  have hM8 := lift_frame [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] fmf cMF
    (fun a n h => out_gen2 h hhi' hz')
  have hW := (out_gen hA hhi' hlh hhi hz').2
  rw [hSm]
  exact ⟨hSsp, hS29, hS28, hS18, hM8.readLE _ _ (out_sp8 hzW (by omega) hhi), hM8.readLE _ _ (out_sp0 hzW (by omega) hhi),
    by rw [hS0]; exact c0.trans (fmf.readLE _ _ (Outside.of_sub hW (Nat.le_refl _) (by omega))),
    by rw [hS1]; exact c1.trans (fmf.readLE _ _ (Outside.of_sub hW (by omega) (by omega))), hM3⟩

theorem post_okt {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {dst pS nS : BitVec 64} {s S S3 Sf : State} {v : Nat}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (cMF : MemFrame S.mem S3.mem [(lo, hi'), (dst.toNat, dst.toNat + 32)])
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hSm : Sf.mem = S3.mem) (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v)
    (c0 : S3.regs 0 = 0) (c1 : S3.regs 1 = 0) (hS0 : Sf.regs 0 = S3.regs 0) (hS1 : Sf.regs 1 = S3.regs 1)
    (cval : Janus.Spec.val256 S3.mem dst.toNat = v) :
    SciPost C R R2 T b L lo hi dst pS nS s Sf := by
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  have hlh : lo ≤ s.sp.toNat := Nat.le_trans (by omega) hlo
  have hz' : dst.toNat = dst.toNat ∨ (lo ≤ dst.toNat ∧ dst.toNat + 32 ≤ s.sp.toNat - 8) := Or.inl rfl
  have hM3 := lift_frame [(lo, hi), (dst.toNat, dst.toNat + 32)] fmf cMF (fun a n h => out_gen h hhi' hlh hhi hz')
  have hM8 := lift_frame [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] fmf cMF
    (fun a n h => out_gen2 h hhi' hz')
  unfold SciPost
  rw [hSm]
  exact ⟨hSsp, hS29, hS28, hS18, hM8.readLE _ _ (out_sp8 hzW (by omega) hhi), hM8.readLE _ _ (out_sp0 hzW (by omega) hhi),
    Or.inl ⟨v, hsci, by rw [hS0]; exact c0, by rw [hS1]; exact c1, cval, hM3⟩⟩

/-- after a successful `SetFromDecimal` call (window `[lo, hi')`, destination `z'`): the body's frame facts still hold -/
theorem fr_next {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {dst pS nS z' : BitVec 64} {s S S3 : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (hz' : z'.toNat = dst.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ s.sp.toNat - 8))
    (k1 : S3.sp = S.sp) (k2 : S3.regs 29 = S.regs 29) (k3 : S3.regs 28 = S.regs 28) (k4 : S3.regs 18 = S.regs 18)
    (k5 : S3.mem.readLE (S.sp.toNat - 8) 8 = S.mem.readLE (S.sp.toNat - 8) 8)
    (k6 : S3.mem.readLE S.sp.toNat 8 = S.mem.readLE S.sp.toNat 8)
    (cMF : MemFrame S.mem S3.mem [(lo, hi'), (z'.toNat, z'.toNat + 32)]) (hreg3 : S3.mem.regions = S.mem.regions) :
    Fr lo dst pS nS s S3 := by
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hfr' := hfr
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hfr'
  have hlh : lo ≤ s.sp.toNat := Nat.le_trans (by omega) hlo
  have hSs : S.sp.toNat + 112 = s.sp.toNat := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have e1 : s.sp.toNat - 112 = S.sp.toNat := by omega
  have e2 : s.sp.toNat - 120 = S.sp.toNat - 8 := by omega
  have hM8 := lift_frame [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] fmf cMF
    (fun a n h => out_gen2 h hhi' hz')
  have hrd : ∀ a n, a = s.sp.toNat + 8 ∨ a = s.sp.toNat + 16 ∨ a = s.sp.toNat + 24 → n = 8 →
      S3.mem.readLE a n = S.mem.readLE a n := by
    intro a n ha hn
    refine cMF.readLE a n ?_
    simp only [outside_cons, outside_nil, and_true]
    rcases hz' with e | e <;> omega
  refine ⟨by rw [k1]; exact fsp, by rw [k3]; exact f28, by rw [k4]; exact f18, by rw [k2]; exact f29, hM8, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg3]; exact freg
  · rw [e1, k6]; rw [← e1]; exact fra
  · rw [e2, k5]; rw [← e2]; exact ffp
  · rw [hrd _ _ (Or.inl rfl) rfl]; exact fdst
  · rw [hrd _ _ (Or.inr (Or.inl rfl)) rfl]; exact fp
  · rw [hrd _ _ (Or.inr (Or.inr rfl)) rfl]; exact fn

/-- The result of a `SetFromDecimal` call made from the body (on the sub-string `(pS + off, nS')`, window `[lo, hi')`, destination `z'`),
when it fails: `SciPost` for the `Sf` reached after the epilogue. -/
theorem post_err {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' off : Nat}
    {dst pS nS z' pS' nS' : BitVec 64} {s S S3 Sf : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (hz' : z'.toNat = dst.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ s.sp.toNat - 8))
    (hsub : (pS'.toNat = pS.toNat + off ∧ off + nS'.toNat ≤ nS.toNat) ∨ nS'.toNat = 0)
    (hpost : TopPost C R R2 T b L lo hi' z' pS' nS' S S3)
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hS0 : Sf.regs 0 = S3.regs 0) (hS1 : Sf.regs 1 = S3.regs 1) (hSm : Sf.mem = S3.mem)
    (hne : ∀ v, decParse (bytesAt s.mem pS'.toNat) nS'.toNat ≠ .ok v)
    (heof : decParse (bytesAt s.mem pS'.toNat) nS'.toNat = .eof → Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .eof)
    (hrange : decParse (bytesAt s.mem pS'.toNat) nS'.toNat = .range → Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .range)
    (hsyn : ∀ l n, decParse (bytesAt s.mem pS'.toNat) nS'.toNat = .syntax l n →
      Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax (off + l) n) :
    SciPost C R R2 T b L lo hi dst pS nS s Sf := by
  have hbS := bytes_xfer C htop hfr
  have hbytes : decParse (bytesAt s.mem pS'.toNat) nS'.toNat = decParse (bytesAt S.mem pS'.toNat) nS'.toNat := by
    rcases hsub with hsub | hsub
    · exact Fv256.I.decParse_congr _ _ _ (fun k hk => by
        have := hbS (off + k) (by omega)
        show s.mem.readLE (pS'.toNat + k) 1 = S.mem.readLE (pS'.toNat + k) 1
        rw [hsub.1, show pS.toNat + off + k = pS.toNat + (off + k) by omega]; exact this.symm)
    · exact Fv256.I.decParse_congr _ _ _ (fun k hk => by omega)
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
  unfold SciPost
  rcases hcases with ⟨v, hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c1, cTe, cMF⟩
  · exact absurd (hbytes.trans hv) (hne v)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := post_eor C htop hlo112 hfr hhi' hz' hE2 c0 c1 cMF hSsp hS29 hS28 hS18 hS0 hS1 hSm
    exact ⟨e1, e2, e3, e4, e5, e6, Or.inr (Or.inl ⟨heof (hbytes.trans hv), e7, e8, e9⟩)⟩
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := post_eor C htop hlo112 hfr hhi' hz' hB2 c0 c1 cMF hSsp hS29 hS28 hS18 hS0 hS1 hSm
    exact ⟨e1, e2, e3, e4, e5, e6, Or.inr (Or.inr (Or.inl ⟨hrange (hbytes.trans hv), e7, e8, e9⟩))⟩
  · have hsub' : pS'.toNat = pS.toNat + off ∧ off + nS'.toNat ≤ nS.toNat := by
      rcases hsub with h | h
      · exact h
      · have := Fv256.I.decParse_syntax _ _ _ _ (hbytes.trans hv); omega
    exact post_syn C htop hlo112 hfr hhi' hz' hsub' (hbytes.trans hv) c0 c1 cTe cMF hSsp hS29 hS28 hS18 hS0 hS1 hSm
      (hsyn lo' len' (hbytes.trans hv))

/-- the tail call `SetFromDecimal(dst, s)` (no `'e'`): all four outcomes give `SciPost` -/
theorem post_tail {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s S S3 Sf : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S) (hhi' : S.sp.toNat + 32 ≤ s.sp.toNat - 8)
    (hpost : TopPost C R R2 T b L lo (S.sp.toNat + 32) dst pS nS S S3)
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hS0 : Sf.regs 0 = S3.regs 0) (hS1 : Sf.regs 1 = S3.regs 1) (hSm : Sf.mem = S3.mem)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt s.mem pS.toNat) nS.toNat) :
    SciPost C R R2 T b L lo hi dst pS nS s Sf := by
  have hbS := bytes_xfer C htop hfr
  have hbytes : decParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt S.mem pS.toNat) nS.toNat :=
    Fv256.I.decParse_congr _ _ _ (fun k hk => (hbS k hk).symm)
  by_cases hok : ∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v
  · obtain ⟨v, hv⟩ := hok
    obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
    rcases hcases with ⟨v', hv', c0, c1, cval, cEnv, cMF⟩ | ⟨hv', -⟩ | ⟨hv', -⟩ | ⟨lo', len', hv', -⟩
    · exact post_okt C htop hlo112 hfr hhi' cMF hSsp hS29 hS28 hS18 hSm (by rw [hsci, hv]) c0 c1 hS0 hS1
        (cval.trans (by have h2 : Res.ok v = Res.ok v' := hv.symm.trans (hbytes.trans hv'); rw [Res.ok.injEq] at h2; exact h2.symm))
    all_goals (have h2 := hv.symm.trans (hbytes.trans hv'); simp at h2)
  · exact post_err C htop hlo112 hfr hhi' (off := 0) (Or.inl rfl) (Or.inl ⟨by omega, by omega⟩) hpost hSsp hS29 hS28 hS18 hS0 hS1 hSm
      (fun v h => hok ⟨v, h⟩) (fun h => by rw [hsci]; exact h) (fun h => by rw [hsci]; exact h) (fun l n h => by rw [hsci, h]; simp)

/-- returning `nil` with `dst` holding the value `v` (a state of the body's frame `Fr`, after the epilogue) -/
theorem post_ok {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s S Sf : State} {v : Nat}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hfr : Fr lo dst pS nS s S)
    (hSsp : Sf.sp = s.sp) (hS29 : Sf.regs 29 = s.regs 29) (hS28 : Sf.regs 28 = s.regs 28) (hS18 : Sf.regs 18 = s.regs 18)
    (hSm : Sf.mem = S.mem) (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v)
    (hS0 : Sf.regs 0 = 0) (hS1 : Sf.regs 1 = 0) (hval : Janus.Spec.val256 S.mem dst.toNat = v) :
    SciPost C R R2 T b L lo hi dst pS nS s Sf := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  have hM3 : MemFrame s.mem S.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    fmf.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
  unfold SciPost
  rw [hSm]
  exact ⟨hSsp, hS29, hS28, hS18, fmf.readLE _ _ (out_sp8 hzW (by omega) hhi), fmf.readLE _ _ (out_sp0 hzW (by omega) hhi),
    Or.inl ⟨v, hsci, hS0, hS1, hval, hM3⟩⟩

/-- the stack facts every body state `S` (with `Fr`) provides -/
theorem frame_facts {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s S : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat) (hFr : Fr lo dst pS nS s S) :
    S.sp.toNat = s.sp.toNat - 112 ∧ S.sp.toNat % 16 = 0 ∧ S.mem.readLE (S.sp.toNat + 136) 8 = nS.toNat ∧
    S.mem.readLE (S.sp.toNat + 128) 8 = pS.toNat ∧ S.mem.readLE (S.sp.toNat + 120) 8 = dst.toNat ∧
    S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat ∧ S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat ∧
    S.mem.accessible (S.sp.toNat - 8) 152 true = true := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, -⟩ := htop
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hFr
  have hSsp : S.sp.toNat = s.sp.toNat - 112 := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine ⟨hSsp, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hSsp, show s.sp.toNat - 112 + 136 = s.sp.toNat + 24 by omega]; exact fn
  · rw [hSsp, show s.sp.toNat - 112 + 128 = s.sp.toNat + 16 by omega]; exact fp
  · rw [hSsp, show s.sp.toNat - 112 + 120 = s.sp.toNat + 8 by omega]; exact fdst
  · rw [hSsp, show s.sp.toNat - 112 - 8 = s.sp.toNat - 120 by omega]; exact ffp
  · rw [hSsp]; exact fra
  · rw [fmf.accessible]
    exact Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)

theorem cmp_z (x y : BitVec 64) : (addSub x y true).snd.z = decide (x = y) := by
  simp [addSub, addWithCarry]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    apply BitVec.eq_of_toNat_eq
    have := x.isLt; have := y.isLt
    omega
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have := x.isLt
    omega

theorem cmp_z32 (x y : BitVec 32) : (addSub x y true).snd.z = decide (x = y) := by
  simp [addSub, addWithCarry]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    apply BitVec.eq_of_toNat_eq
    have := x.isLt; have := y.isLt
    omega
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have := x.isLt
    omega

theorem mask_pos (d x : BitVec 64) (h1 : 0 < d.toNat) (h2 : d.toNat < 2^63) : x &&& (0#64 - d).sshiftRight 63 = x := by
  have hm : (0#64 - d).msb = true := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [decide_eq_true_eq]
    omega
  have : (0#64 - d).sshiftRight 63 = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sshiftRight_of_msb_true hm]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_allOnes]
    omega
  rw [this, BitVec.and_allOnes]

theorem mask_zero (x : BitVec 64) : x &&& (0#64 - 0#64).sshiftRight 63 = 0 := by simp

theorem fr_of_eq {lo : Nat} {dst pS nS : BitVec 64} {s S S' : State} (hfr : Fr lo dst pS nS s S)
    (h1 : S'.sp = S.sp) (h28 : S'.regs 28 = S.regs 28) (h18 : S'.regs 18 = S.regs 18) (h29 : S'.regs 29 = S.regs 29)
    (hm : S'.mem = S.mem) : Fr lo dst pS nS s S' := by
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hfr
  unfold Fr
  rw [h1, h28, h18, h29, hm]
  exact ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩

/-! ## the callee summaries `scanScientificFromString` needs besides `SetFromDecimal` and `IndexByteString` -/

/-- precondition of `(*Int).Exp` (arm64), as in `Fv256.Arm64.ExpMain.exp_summary` with the data-loaded predicate `D` -/
def ExpPre (D : Janus.Arm64.Memory → Prop) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 32 ∧ StackOK s 168 40 ∧ 336 ≤ s.sp.toNat ∧
    Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 168) 208 ∧
    (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
    (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
    (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
    Apart (s.regs 0).toNat 32 (s.sp.toNat - 168) 208 ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 168) 208 ∧
    Apart (s.regs 2).toNat 32 (s.sp.toNat - 168) 208 ∧ D s.mem

/-- postcondition of `(*Int).Exp` (arm64), as `Fv256.Arm64.ExpMain.PostE` -/
def ExpPost (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
    s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
    s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.expSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
    MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 168, s.sp.toNat - 8),
      (s.sp.toNat + 8, s.sp.toNat + 32)]

/-- precondition of `(*Int).MulOverflow` (arm64), as in `Fv256.Arm64.MoSa.correctness` -/
def MoPreS (z x y : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
    Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
    Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
    Disjoint y.toNat 32 (s.sp.toNat - 240) 256

/-- postcondition of `(*Int).MulOverflow` (arm64), as in `Fv256.Arm64.MoSa.correctness` (with the callee-saved registers) -/
def MoPostS (z x y : BitVec 64) (s s' : State) : Prop :=
  (s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 18 = s.regs 18) ∧
  (s'.regs 0 = z ∧
    (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
    val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
    Fv256.UtilSa.OnlyWrites3 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 232 (s.sp.toNat + 8) 8)

/-- facts about a 32-byte local inside the window `[lo, hi)` that `toppre_sub` needs of the destination -/
theorem local_facts {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) {z' : Nat} (hz1 : lo ≤ z') (hz2 : z' + 32 ≤ hi) :
    (Outside z' 32 R.rt ∨ InRanges z' 32 L) ∧ Outside z' 32 R2.priv ∧
    (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z', z' + 32)]) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ z' ∨ z' + 32 ≤ (s.regs 28).toNat + 16) := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, -⟩ := hEnv
  refine ⟨Or.inl (Outside.of_sub hr9 hz1 (by omega)), Outside.of_sub hr10 hz1 (by omega), fun r hr => ?_, ?_⟩
  · have := hr14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · omega

/-- the arguments of the second `SetFromDecimal` call (`s[idx+1:]`) -/
theorem exp_args {pS nS p1 p2 : BitVec 64} {i : Nat} (hi : i < nS.toNat) (hP48 : pS.toNat + nS.toNat ≤ 2 ^ 48)
    (hx1 : (nS.toNat = i + 1 → p1 = pS) ∧ (i + 1 < nS.toNat → p1 = pS + BitVec.ofNat 64 (i + 1)))
    (hx2 : p2 = nS - BitVec.ofNat 64 (i + 1)) :
    p2.toNat = nS.toNat - (i + 1) ∧
    (p2.toNat = 0 ∨ (pS.toNat ≤ p1.toNat ∧ p1.toNat + p2.toNat ≤ pS.toNat + nS.toNat)) ∧
    p1.toNat + p2.toNat ≤ 2 ^ 48 ∧ (p2.toNat = 0 ∨ p1.toNat = pS.toNat + (i + 1)) := by
  have hn := nS.isLt
  have hpS := pS.isLt
  have hn2 : p2.toNat = nS.toNat - (i + 1) := by
    rw [hx2]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine ⟨hn2, ?_⟩
  by_cases hc1 : nS.toNat = i + 1
  · have := hx1.1 hc1
    subst this
    refine ⟨Or.inl (by omega), by omega, Or.inl (by omega)⟩
  · have h1 := hx1.2 (by omega)
    have e1 : p1.toNat = pS.toNat + (i + 1) := by
      rw [h1]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show pS.toNat + (i + 1) < 2 ^ 64 by omega)]
    refine ⟨Or.inr ⟨by omega, by omega⟩, by omega, Or.inr e1⟩

/-- the arithmetic facts of `TopPre` (no disjunctions, so that `omega` stays fast) -/
theorem top_nums {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    lo ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ hi ∧ hi ≤ 2 ^ 48 ∧ lo + 4528 ≤ s.sp.toNat ∧ pS.toNat + nS.toNat ≤ 2 ^ 48 ∧
    s.mem.accessible lo (hi - lo) true = true := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv
  exact ⟨hr1, hhi, hr3, hlo, hP48, hr5⟩

/-- `Fr` is kept by changes to the 72 bytes of locals `[S.sp+32, S.sp+104)` -/
theorem fr_loc {lo : Nat} {dst pS nS : BitVec 64} {s S S' : State} (hfr : Fr lo dst pS nS s S)
    (h112 : 112 ≤ s.sp.toNat) (hlo : lo ≤ S.sp.toNat + 32) (hF : MemFrame S.mem S'.mem [(S.sp.toNat + 32, S.sp.toNat + 104)])
    (hreg : S'.mem.regions = S.mem.regions) (h1 : S'.sp = S.sp) (h28 : S'.regs 28 = S.regs 28)
    (h18 : S'.regs 18 = S.regs 18) (h29 : S'.regs 29 = S.regs 29) : Fr lo dst pS nS s S' := by
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hfr
  have hSsp : S.sp.toNat = s.sp.toNat - 112 := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ S.sp.toNat + 32 ∨ S.sp.toNat + 104 ≤ a) → S'.mem.readLE a n = S.mem.readLE a n := by
    intro a n ha
    refine hF.readLE a n ?_
    simp only [outside_cons, outside_nil, and_true]; exact ha
  refine ⟨by rw [h1]; exact fsp, by rw [h28]; exact f28, by rw [h18]; exact f18, by rw [h29]; exact f29, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine fmf.trans hF (fun a n ho => ⟨ho, ?_⟩)
    simp only [outside_cons, outside_nil, and_true] at ho ⊢
    omega
  · rw [hreg]; exact freg
  · rw [hrd _ _ (Or.inl (by omega))]; exact fra
  · rw [hrd _ _ (Or.inl (by omega))]; exact ffp
  · rw [hrd _ _ (Or.inr (by omega))]; exact fdst
  · rw [hrd _ _ (Or.inr (by omega))]; exact fp
  · rw [hrd _ _ (Or.inr (by omega))]; exact fn

theorem exp_bytes_eq {m : Janus.Arm64.Memory} {pS pS' : BitVec 64} {nS n' i : Nat} (hn' : n' = nS - (i + 1))
    (hp : n' = 0 ∨ pS'.toNat = pS.toNat + (i + 1)) :
    decParse (bytesAt m pS'.toNat) n' = decParse (fun k => bytesAt m pS.toNat (i + 1 + k)) (nS - (i + 1)) := by
  rw [← hn']
  exact Fv256.I.decParse_congr _ _ _ (fun k hk => by
    rcases hp with h | h
    · omega
    · show m.readLE (pS'.toNat + k) 1 = m.readLE (pS.toNat + (i + 1 + k)) 1
      rw [h, show pS.toNat + (i + 1) + k = pS.toNat + (i + 1 + k) by omega])

/-- the two outcomes of a `SetFromDecimal` call, as the caller's `CBNZ X0` sees them -/
theorem post_dichot {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi' : Nat}
    {dst pS nS z' pS' nS' : BitVec 64} {s S S3 : State}
    (htop : TopPre C R R2 T b L lo hi dst pS nS s) (hlo112 : lo + 4640 ≤ s.sp.toNat)
    (hinit : InitDone C R2 s.mem) (hitab : BitVec.ofNat 64 C.numErrItab ≠ 0)
    (hfr : Fr lo dst pS nS s S) (hhi' : hi' ≤ s.sp.toNat - 8)
    (hz' : z'.toNat = dst.toNat ∨ (lo ≤ z'.toNat ∧ z'.toNat + 32 ≤ s.sp.toNat - 8))
    (hpost : TopPost C R R2 T b L lo hi' z' pS' nS' S S3) :
    (S3.regs 0 = 0 ∧ ∃ v, decParse (bytesAt S.mem pS'.toNat) nS'.toNat = .ok v ∧ S3.regs 1 = 0 ∧
        Janus.Spec.val256 S3.mem z'.toNat = v ∧ MemFrame S.mem S3.mem [(lo, hi'), (z'.toNat, z'.toNat + 32)]) ∨
    (S3.regs 0 ≠ 0 ∧ ∀ v, decParse (bytesAt S.mem pS'.toNat) nS'.toNat ≠ .ok v) := by
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  obtain ⟨i1, i2, i3, i4, -⟩ := hinit
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
  have hlh : lo ≤ s.sp.toNat := Nat.le_trans (by omega) hlo
  have hI0 : ∀ (a n : Nat), Outside a n [(lo, hi), (dst.toNat, dst.toNat + 32)] →
      Outside a n [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)] :=
    fun a n h => (out_gen (hi' := hi') (z' := z'.toNat) h hhi' hlh hhi hz').2
  rcases hcases with ⟨v, hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c1, cTe, cMF⟩
  · exact Or.inl ⟨by simpa using c0, v, hv, by simpa using c1, cval, cMF⟩
  · refine Or.inr ⟨?_, fun v h => by rw [hv] at h; simp at h⟩
    intro h0'; rw [h0'] at c0
    have := c0.trans (fmf.readLE _ _ (Outside.of_sub (hI0 _ _ hE2) (Nat.le_refl _) (by omega)))
    simp at this; exact i1 this.symm
  · refine Or.inr ⟨?_, fun v h => by rw [hv] at h; simp at h⟩
    intro h0'; rw [h0'] at c0
    have := c0.trans (fmf.readLE _ _ (Outside.of_sub (hI0 _ _ hB2) (Nat.le_refl _) (by omega)))
    simp at this; exact i3 this.symm
  · exact Or.inr ⟨by rw [c0]; exact hitab, fun v h => by rw [hv] at h; simp at h⟩

theorem top_zW {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, -⟩ := htop
  exact hzW

theorem dst_out2 {dst lo hi hi' z' : Nat} (hzW : dst + 32 ≤ lo ∨ hi ≤ dst) (h1 : lo ≤ z') (h2 : z' + 32 ≤ hi) (h3 : hi' ≤ hi) :
    Outside dst 32 [(lo, hi'), (z', z' + 32)] := by
  simp only [outside_cons, outside_nil, and_true]; omega

theorem e1_ne (i : Nat) (h : i + 1 < 2 ^ 64) : (addWithCarry (BitVec.ofNat 64 i) (1#64) false).snd.z = false := by
  simp [addWithCarry]
  intro h2
  have := congrArg BitVec.toNat h2
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem top_zR {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    Outside dst.toNat 32 R.rt ∨ InRanges dst.toNat 32 L := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  exact hzR

theorem top_zPr {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    Outside dst.toNat 32 R2.priv := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  exact hzPr

theorem top_zS {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(dst.toNat, dst.toNat + 32)] := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  exact hzS

theorem top_zg {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    (s.regs 28).toNat + 16 + 8 ≤ dst.toNat ∨ dst.toNat + 32 ≤ (s.regs 28).toNat + 16 := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop
  exact hzg

theorem top_zP {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst pS nS : BitVec 64} {s : State} (htop : TopPre C R R2 T b L lo hi dst pS nS s) :
    Ptr32 s.mem dst true := by
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, -⟩ := htop
  exact hzP

end Fv256.Arm64.ScanSciSpec
