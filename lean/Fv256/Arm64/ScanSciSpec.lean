import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.DecCongr
import Fv256.IndexByteSpec
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.FromDecimalSpec

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
  TopPre C R R2 T b L lo hi dst pS nS s ∧ lo + 4632 ≤ s.sp.toNat ∧
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
    (hlo : lo + 4520 ≤ S.sp.toNat) (hhi : S.sp.toNat + 32 ≤ hi')
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
    refine Fv256.Arm64.FromDecimalSpec.chunkOK_mono C this (fun r hr => hr) hhi' ?_
    rw [hF.accessible]; exact this.2.2.2.1

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

end Fv256.Arm64.ScanSciSpec
