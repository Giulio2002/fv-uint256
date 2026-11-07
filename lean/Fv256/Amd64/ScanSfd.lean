import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.SpecScan
import Fv256.DecCongr
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.ScanSpec

/-!
# `scanScientificFromString`: the `SetFromDecimal` call sites (Extracted-free)

`toppre_sub`: from `TopPre0` at the entry of `scanScientificFromString` (receiver `dst`, string `(p, n)`, window `[lo, hi)`) to `TopPre0`
for a `SetFromDecimal` call from the state `S3` inside the frame (window `[lo, hi3)`, receiver `z'` = `dst` or a local `Int`, string = a
sub-range `(p', n')`).  `scanStr_of_top`: the result of such a call, as `ScanStrPost` for the whole string.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec

namespace Fv256.Amd64.ScanSfd

/-- an opaque wrapper: keeps a big hypothesis out of the stepper's hypothesis search -/
def Hid (p : Prop) : Prop := p

variable (C : SfdCfg)

set_option maxRecDepth 100000

theorem chunkOK_mono' {R : RtInv} {R2 : IfaceModel} {L : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64} {lo hi hi3 : Nat}
    {m m' : Janus.Arm64.Memory} (h : ChunkOK C R R2 L b sp sl lo hi m) (hh : hi3 ≤ hi)
    (hacc : m'.accessible sp.toNat sl.toNat false = true) : ChunkOK C R R2 L b sp sl lo hi3 m' :=
  Fv256.Amd64.FromDecimalSpec.chunkOK_mono C h (fun r hr => hr) hh hacc

theorem toppre_sub {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat}
    {dst p n z' p' n' : BitVec 64} {s S3 : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hh3 : hi3 ≤ hi)
    (hF : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hEnv3 : Env C R R2 T b L lo hi3 S3)
    (hr0 : S3.regs 0 = z') (hr3 : S3.regs 3 = p') (hr1 : S3.regs 1 = n')
    (hr4 : lo + 4800 ≤ (S3.regs 4).toNat) (hr4' : (S3.regs 4).toNat + 32 ≤ hi3)
    (hsub1 : p.toNat ≤ p'.toNat) (hsub2 : p'.toNat + n'.toNat ≤ p.toNat + n.toNat)
    (hzO : ∀ a k, Outside a k [(lo, hi), (dst.toNat, dst.toNat + 32)] → Outside a k [(lo, hi3), (z'.toNat, z'.toNat + 32)])
    (hzB : Buffer S3 z' 32 true) (hzW : z'.toNat + 32 ≤ lo ∨ hi3 ≤ z'.toNat)
    (hzR : Outside z'.toNat 32 R.rt ∨ InRanges z'.toNat 32 L) (hzP : Outside z'.toNat 32 R2.priv)
    (hzS : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z'.toNat, z'.toNat + 32)])
    (hzG : (S3.regs 14).toNat + 16 + 8 ≤ z'.toNat ∨ z'.toNat + 32 ≤ (S3.regs 14).toNat + 16)
    (hzp : n'.toNat = 0 ∨ p'.toNat + n'.toNat ≤ z'.toNat ∨ z'.toNat + 32 ≤ p'.toNat) :
    TopPre0 C R R2 T b L lo hi3 z' p' n' S3 := by
  obtain ⟨-, -, -, hMod, -, -, -, hMult, hE1, hE2, hB1, hB2, hMa, hMo, hMr, hMb, -, -, -, -, -, -, ⟨hP48, hPa⟩, hPW, -, hCh⟩ := hp
  obtain ⟨u1, u2, u3⟩ := hMult
  have hrd : ∀ a k, Outside a k [(lo, hi), (dst.toNat, dst.toNat + 32)] → S3.mem.readLE a k = s.mem.readLE a k :=
    fun a k h => hF.readLE a k h
  unfold TopPre0
  refine ⟨hr0, hr3, hr1, hMod, hEnv3, hr4, hr4', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hzB, hzW, hzR, hzP, hzS, hzG, ?_, ?_, hzp, ?_⟩
  · -- MultOK
    refine ⟨by rw [hF.accessible]; exact u1, hzO _ _ u2, ?_⟩
    intro k hk1 hk2
    obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
    have hread : S3.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 := by
      refine hrd _ _ ?_
      have := Outside.of_sub u2 (a := C.mulTab + 8 * k) (n := 8) (by omega) (by omega)
      exact this
    rw [hread]
    refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, hzO _ _ v4⟩
    have : S3.mem.readLE (s.mem.readLE (C.mulTab + 8 * k) 8) 32 = s.mem.readLE (s.mem.readLE (C.mulTab + 8 * k) 8) 32 := hrd _ _ v4
    unfold Janus.Spec.val256 at v3 ⊢
    rw [this]; exact v3
  · rw [hF.accessible]; exact hE1
  · exact hzO _ _ hE2
  · rw [hF.accessible]; exact hB1
  · exact hzO _ _ hB2
  · rw [hF.accessible]; exact hMa
  · exact hzO _ _ hMo
  · exact hMr
  · intro k hk
    rw [hrd _ _ (Outside.of_sub hMo (a := C.maxStr + k) (n := 1) (by omega) (by omega))]
    exact hMb k hk
  · refine ⟨by omega, ?_⟩
    by_cases h0 : n'.toNat = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases hPa with h | h
      · omega
      · rw [hF.accessible]
        exact Janus.Arm64.Memory.accessible_sub s.mem h (Or.inl rfl) hsub1 hsub2
  · by_cases h0 : n'.toNat = 0
    · exact Or.inl h0
    · rcases hPW with h | h | h
      · omega
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
  · intro sp sl h1 h2 h3 h4
    have := hCh sp sl (by omega) (by omega) h3 h4
    refine chunkOK_mono' C this hh3 ?_
    rw [hF.accessible]; exact this.2.2.2.1

/-- the environment of the shrunk window `[lo, hi3)` at a state `S3` reached from `s` by stores inside the window -/
theorem env_sub {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat} {s S3 : State}
    (hMod : Mod C R R2 T L) (hEnv : Env C R R2 T b L lo hi s) (hF : MemFrame s.mem S3.mem [(lo, hi)])
    (hr14 : S3.regs 14 = s.regs 14) (hh3 : hi3 ≤ hi) (h4 : lo ≤ (S3.regs 4).toNat)
    (h4' : (S3.regs 4).toNat + 8 ≤ hi3) (h8 : (S3.regs 4).toNat % 8 = 0) :
    Env C R R2 T b L lo hi3 S3 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := hMod
  have hgz : (S3.regs 14).toNat = (s.regs 14).toNat := by rw [hr14]
  have e5s : s.mem.accessible lo (hi3 - lo) true = true :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have e9s : Outside lo (hi3 - lo) R.rt := Outside.of_sub e9 (Nat.le_refl _) (by omega)
  have e10s : Outside lo (hi3 - lo) R2.priv := Outside.of_sub e10 (Nat.le_refl _) (by omega)
  have e13s : (s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi3 ≤ (s.regs 14).toNat + 16 := by omega
  have e14s : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(lo, hi3)] := by
    intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  have e18s : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [(lo, hi3)] := by
    intro r hr
    have := e18 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  refine ⟨h4, h4', by omega, h8, ?_, by rw [hgz]; exact e6, ?_, ?_, e9s, e10s, by rw [hgz]; exact e11,
    by rw [hgz]; exact e12, by rw [hgz]; exact e13s, e14s, ?_, ?_, ?_, e18s⟩
  · rw [hF.accessible]; exact e5s
  · rw [hgz, hF.accessible]; exact e7
  · rw [hgz, hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
  · refine StaticOK.frame e15 hF ?_
    intro r hr
    exact e14 r hr
  · rw [hr14]; refine m1.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
    intro a ha
    obtain ⟨r, hr, h1, h2⟩ := ha
    have a1 := MemFrame.outside_mem e10 hr
    simp only [outside_cons, outside_nil, and_true]
    omega
  · rw [hgz]
    exact RtInv.inv_frame' (ws := [(lo, hi)]) hF (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Or.inl e9) e17

/-- the bytes of the string are the same in the call state `S3` as in the entry state `s` -/
theorem str_same {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst p n : BitVec 64} {s : State} {M3 : Janus.Arm64.Memory}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s)
    (hF : MemFrame s.mem M3 [(lo, hi), (dst.toNat, dst.toNat + 32)]) :
    ∀ k, k < n.toNat → bytesAt M3 p.toNat k = bytesAt s.mem p.toNat k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPW, hPz, -⟩ := hp
  intro k hk
  unfold bytesAt
  refine hF.readLE _ _ ?_
  simp only [outside_cons, outside_nil, and_true]
  have h0 : ¬ n.toNat = 0 := by omega
  rcases hPW with h | h | h
  · omega
  · rcases hPz with h' | h' | h'
    · omega
    · exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
    · exact ⟨Or.inl (by omega), Or.inr (by omega)⟩
  · rcases hPz with h' | h' | h'
    · omega
    · exact ⟨Or.inr (by omega), Or.inl (by omega)⟩
    · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩

theorem frame_top {R : RtInv} {R2 : IfaceModel} {lo hi hi3 : Nat} {dst z : BitVec 64} {m0 M3 M' : Janus.Arm64.Memory}
    (hh3 : hi3 ≤ hi) (hzin : (z = dst) ∨ (lo ≤ z.toNat ∧ z.toNat + 32 ≤ hi))
    (hF : MemFrame m0 M3 [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hW : Outside lo (hi - lo) R.rt) (hW2 : Outside lo (hi - lo) R2.priv)
    (hq : MemFrame M3 M' [(lo, hi3), (z.toNat, z.toNat + 32)] ∨ MemFrame M3 M' (R.rt ++ R2.priv ++ [(lo, hi3), (z.toNat, z.toNat + 32)])) :
    MemFrame m0 M' (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := by
  have hbig : ∀ a k, Outside a k (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) →
      Outside a k [(lo, hi), (dst.toNat, dst.toNat + 32)] := by
    intro a k h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact h.2
  have hz : ∀ a k, Outside a k (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) →
      Outside a k [(lo, hi3), (z.toNat, z.toNat + 32)] := by
    intro a k h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    refine ⟨by omega, ?_⟩
    rcases hzin with rfl | ⟨e1, e2⟩
    · exact h4
    · omega
  have hz2 : ∀ a k, Outside a k (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) →
      Outside a k (R.rt ++ R2.priv ++ [(lo, hi3), (z.toNat, z.toNat + 32)]) := by
    intro a k h
    have h' := hz a k h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h h' ⊢
    exact ⟨h.1, h'⟩
  rcases hq with hq | hq
  · exact hF.trans hq (rs'' := R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨hbig a k h, hz a k h⟩)
  · exact hF.trans hq (rs'' := R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨hbig a k h, hz2 a k h⟩)

theorem scanStr_top {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 off : Nat}
    {dst p n z p' n' : BitVec 64} {s S3 S' F : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hh3 : hi3 ≤ hi)
    (hF : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hzin : (z = dst) ∨ (lo ≤ z.toNat ∧ z.toNat + 32 ≤ hi))
    (hpost : TopPost C R R2 T b L lo hi3 z p' n' S3 S')
    (hFm : F.mem = S'.mem) (hF0 : F.regs 0 = S'.regs 0) (hF3 : F.regs 3 = S'.regs 3)
    (hp'off : p'.toNat = p.toNat + off) (hsub : off + n'.toNat ≤ n.toNat)
    (hok : ∀ v, decParse (bytesAt S3.mem p'.toNat) n'.toNat = .ok v → Janus.Spec.val256 S'.mem z.toNat = v →
      sciParse (bytesAt s.mem p.toNat) n.toNat = .ok v ∧ Janus.Spec.val256 S'.mem dst.toNat = v)
    (heof : decParse (bytesAt S3.mem p'.toNat) n'.toNat = .eof → sciParse (bytesAt s.mem p.toNat) n.toNat = .eof)
    (hrange : decParse (bytesAt S3.mem p'.toNat) n'.toNat = .range → sciParse (bytesAt s.mem p.toNat) n.toNat = .range)
    (hsyn : ∀ l m, decParse (bytesAt S3.mem p'.toNat) n'.toNat = .syntax l m →
      sciParse (bytesAt s.mem p.toNat) n.toNat = .syntax (off + l) m) :
    ScanStrPost C R b L lo hi dst p n s F ∧ MemFrame s.mem F.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := by
  have hp0 := hp
  obtain ⟨-, -, -, hMod, hEnv, -, -, -, hE1, hE2, hB1, hB2, -, -, -, -, -, -, -, -, hzS, -, ⟨hP48, -⟩, hPW, hPz, -⟩ := hp0
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -⟩ := hEnv'
  obtain ⟨hKept, hcases⟩ := hpost
  have hmf : ∀ rs' : List (Nat × Nat), MemFrame S3.mem S'.mem rs' → (∀ a k, Outside a k (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) → Outside a k rs') → MemFrame s.mem S'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := by
    intro rs' hq hrs
    have hF' : MemFrame s.mem S3.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := hF.mono (fun a k h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2)
    exact hF'.trans hq (rs'' := R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, hrs a k h⟩)
  have hsame := str_same C hp hF
  have hio : ∀ a, (C.ioEOF ≤ a ∧ a + 8 ≤ C.ioEOF + 16) → S3.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    refine hF.readLE a 8 ?_
    simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
    omega
  have hereg : ∀ a, (C.errBig ≤ a ∧ a + 8 ≤ C.errBig + 16) → S3.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    refine hF.readLE a 8 ?_
    simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
    omega
  have hzr : ∀ rs' : List (Nat × Nat), (∀ a k, Outside a k (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) → Outside a k rs') →
      Outside lo (hi - lo) R.rt → True := fun _ _ _ => trivial
  rcases hcases with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨l2, m2, hv, q, t, c0, c3, cTe, cMF⟩
  · obtain ⟨h1, h2⟩ := hok v hv cval
    refine ⟨Or.inl ⟨v, h1, by rw [hF0]; exact c0, by rw [hF3]; exact c3, by rw [hFm]; exact h2⟩, ?_⟩
    rw [hFm]
    refine hmf _ cMF ?_
    intro a k h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    rcases hzin with rfl | ⟨g1, g2⟩
    · exact ⟨by omega, h.2.2⟩
    · exact ⟨by omega, by omega⟩
  · refine ⟨Or.inr (Or.inl ⟨heof hv, ?_, ?_⟩), ?_⟩
    · rw [hF0, c0]; exact hio _ ⟨Nat.le_refl _, by omega⟩
    · rw [hF3, c3]; exact hio _ ⟨by omega, by omega⟩
    · rw [hFm]
      refine hmf _ cMF ?_
      intro a k h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      rcases hzin with rfl | ⟨g1, g2⟩
      · exact ⟨by omega, h.2.2⟩
      · exact ⟨by omega, by omega⟩
  · refine ⟨Or.inr (Or.inr (Or.inl ⟨hrange hv, ?_, ?_⟩)), ?_⟩
    · rw [hF0, c0]; exact hereg _ ⟨Nat.le_refl _, by omega⟩
    · rw [hF3, c3]; exact hereg _ ⟨by omega, by omega⟩
    · rw [hFm]
      refine hmf _ cMF ?_
      intro a k h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      rcases hzin with rfl | ⟨g1, g2⟩
      · exact ⟨by omega, h.2.2⟩
      · exact ⟨by omega, by omega⟩
  · have hsy := hsyn l2 m2 hv
    have hdp := Fv256.I.decParse_syntax _ _ _ _ hv
    obtain ⟨hm0, hlm, -⟩ := hdp
    obtain ⟨te1, te2, te3, te4, te5, te6, te7, te8, te9, te10, te11, -⟩ := cTe
    refine ⟨Or.inr (Or.inr (Or.inr ⟨off + l2, m2, hsy, q, t, by rw [hF0]; exact c0, by rw [hF3]; exact c3, ?_⟩)), ?_⟩
    · have hmem : (C.strconvErrSyntax, C.strconvErrSyntax + 16) ∈ staticRanges C T := by simp [staticRanges]
      have hs1 := e14 _ hmem
      have hs2 := hzS _ hmem
      have hro : ∀ a, C.strconvErrSyntax ≤ a → a + 8 ≤ C.strconvErrSyntax + 16 → S3.mem.readLE a 8 = s.mem.readLE a 8 := by
        intro a ha1 ha2
        refine hF.readLE a 8 ?_
        simp only [outside_cons, outside_nil, and_true] at hs1 hs2 ⊢
        omega
      have hpn : (BitVec.ofNat 64 (p.toNat + (off + l2))).toNat = p.toNat + (off + l2) := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hP48; omega)
      have hpn1 : (BitVec.ofNat 64 (p'.toNat + l2)).toNat = p.toNat + (off + l2) := by
        rw [BitVec.toNat_ofNat, hp'off, Nat.add_assoc]; exact Nat.mod_eq_of_lt (by have := hP48; omega)
      unfold SynObj
      rw [hFm]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact te1
      · exact te2
      · exact te3
      · exact te4
      · exact te5
      · exact te6
      · exact te7
      · exact te8
      · rw [te9, hro _ (Nat.le_refl _) (by omega)]
      · rw [te10, hro _ (by omega) (by omega)]
      · intro k hk
        rw [te11 k hk, hpn1, hpn]
        have hm2 : (BitVec.ofNat 64 m2).toNat = m2 := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := n'.isLt; omega)
        rw [hm2] at hk
        have := hsame (off + l2 + k) (by omega)
        unfold bytesAt at this
        rw [show p.toNat + (off + l2) + k = p.toNat + (off + l2 + k) by omega]
        exact this
    · rw [hFm]
      refine hmf _ cMF ?_
      intro a k h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      rcases hzin with rfl | ⟨g1, g2⟩
      · exact ⟨h.1, by omega, h.2.2⟩
      · exact ⟨h.1, by omega, by omega⟩

/-- the `TopPre` of the `SetFromDecimal(dst, p, n')` calls made directly from the frame of `scanScientificFromString` (the tail call
and the call on the mantissa): the call state `S3` is the state `S` after the `IndexByteString` call plus the pushed return address `ra` -/
theorem call_pre1 {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi ra : Nat}
    {dst p n n' : BitVec 64} {s S S3 : State}
    (hret0 : RetOK s) (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hlo : lo + 4920 ≤ (s.regs 4).toNat)
    (kmf : MemFrame s.mem S.mem [(lo, hi)]) (hra : ra < 2 ^ 47)
    (hmem : S3.mem = S.mem.writeLE ((s.regs 4).toNat - 120) 8 ra)
    (h4 : S3.regs 4 = s.regs 4 - 120#64) (h0 : S3.regs 0 = dst) (h3 : S3.regs 3 = p) (h1 : S3.regs 1 = n')
    (h14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false) (hn' : n'.toNat ≤ n.toNat) :
    TopPre C R R2 T b L lo ((s.regs 4).toNat - 88) dst p n' S3 := by
  have hp0 := hp
  obtain ⟨-, -, -, hMod, hEnv, -, hhi, -, -, -, -, -, -, -, -, -, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, -⟩ := hp0
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := hEnv'
  have hsp := (s.regs 4).isLt
  have hs4 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by
    rw [h4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hF1 : MemFrame s.mem S3.mem [(lo, hi)] := by
    rw [hmem]; exact kmf.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF2 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hF1.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  have hE3 : Env C R R2 T b L lo ((s.regs 4).toNat - 88) S3 :=
    env_sub C hMod hEnv hF1 h14 (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, toppre_sub C hp (by omega) hF2 hE3 h0 h3 h1 (by omega) (by omega) (Nat.le_refl _) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · unfold RetOK
    rw [hs4, hF1.accessible, hmem, Janus.Arm64.Memory.readLE_writeLE_self]
    refine ⟨?_, ?_, hx15, hdf⟩
    · exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
    · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hra
  · intro a k h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  · exact ⟨hzw, by rw [hF1.accessible]; exact hz⟩
  · omega
  · exact hzR
  · exact hzP
  · exact hzS
  · rw [h14]; exact hzg
  · by_cases h0' : n'.toNat = 0
    · exact Or.inl h0'
    · rcases (show n.toNat = 0 ∨ p.toNat + n.toNat ≤ dst.toNat ∨ dst.toNat + 32 ≤ p.toNat from by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hp; exact h) with h | h | h
      · omega
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)

/-- a `SetFromDecimal(dst, ..)` call with window `[lo, hi3)` keeps the frame words above it -/
theorem top_keep {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat}
    {dst p n p' n' : BitVec 64} {s S3 S' : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s)
    (hpost : TopPost C R R2 T b L lo hi3 dst p' n' S3 S') (hlh : lo ≤ hi3) (a k : Nat) (h1 : hi3 ≤ a) (h2 : a + k ≤ hi) :
    S'.mem.readLE a k = S3.mem.readLE a k := by
  obtain ⟨-, -, -, -, hEnv, -, -, -, -, -, -, -, -, -, -, -, -, hzW, -⟩ := hp
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, -⟩ := hEnv
  obtain ⟨-, hcases⟩ := hpost
  have ho1 : Outside a k [(lo, hi3), (dst.toNat, dst.toNat + 32)] := by
    simp only [outside_cons, outside_nil, and_true]
    omega
  have ho2 : Outside a k (R.rt ++ R2.priv ++ [(lo, hi3), (dst.toNat, dst.toNat + 32)]) := by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨?_, ?_⟩, by omega, by omega⟩
    · exact Outside.of_sub e9 (by omega) (by omega)
    · exact Outside.of_sub e10 (by omega) (by omega)
  rcases hcases with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨l2, m2, hv, q, t, c0, c3, cTe, cMF⟩
  · exact cMF.readLE a k ho1
  · exact cMF.readLE a k ho1
  · exact cMF.readLE a k ho1
  · exact cMF.readLE a k ho2

/-- accessibility is unchanged by a `SetFromDecimal` call -/
theorem top_acc {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z p n : BitVec 64} {S3 S' : State} (hpost : TopPost C R R2 T b L lo hi z p n S3 S') (a k : Nat) (w : Bool) :
    S'.mem.accessible a k w = S3.mem.accessible a k w := by
  obtain ⟨-, hcases⟩ := hpost
  rcases hcases with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨l2, m2, hv, q, t, c0, c3, cTe, cMF⟩
  · exact cMF.accessible a k w
  · exact cMF.accessible a k w
  · exact cMF.accessible a k w
  · exact cMF.accessible a k w

/-! projections of `TopPre0` -/
section proj
variable {C : SfdCfg} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z p n : BitVec 64} {s : State}

theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.mod (h : TopPre0 C R R2 T b L lo hi z p n s) : Mod C R R2 T L := h.2.2.2.1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.env (h : TopPre0 C R R2 T b L lo hi z p n s) : Env C R R2 T b L lo hi s := h.2.2.2.2.1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.lo4 (h : TopPre0 C R R2 T b L lo hi z p n s) : lo + 4800 ≤ (s.regs 4).toNat := h.2.2.2.2.2.1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.hi32 (h : TopPre0 C R R2 T b L lo hi z p n s) : (s.regs 4).toNat + 32 ≤ hi := h.2.2.2.2.2.2.1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.pw (h : TopPre0 C R R2 T b L lo hi z p n s) : p.toNat + n.toNat ≤ 2 ^ 48 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h1, -⟩, -⟩ := h
  exact h1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.pacc (h : TopPre0 C R R2 T b L lo hi z p n s) : n.toNat = 0 ∨ s.mem.accessible p.toNat n.toNat false = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, h1⟩, -⟩ := h
  exact h1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.pwin (h : TopPre0 C R R2 T b L lo hi z p n s) : n.toNat = 0 ∨ p.toNat + n.toNat ≤ lo ∨ hi ≤ p.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := h
  exact h1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.pz (h : TopPre0 C R R2 T b L lo hi z p n s) : n.toNat = 0 ∨ p.toNat + n.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ p.toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := h
  exact h1
theorem _root_.Fv256.Amd64.SfdTopSpec.TopPre0.chunk (h : TopPre0 C R R2 T b L lo hi z p n s) : ChunkAll C R R2 L b p.toNat n.toNat lo hi s.mem := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := h
  exact h1
end proj

end Fv256.Amd64.ScanSfd
