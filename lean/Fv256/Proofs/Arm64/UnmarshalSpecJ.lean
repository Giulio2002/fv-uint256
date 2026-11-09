import Fv256.Proofs.Arm64.UnmarshalSpec
import Fv256.Proofs.Arm64.SbtsFacts
import Fv256.Spec.Arm64.UnmarshalSpecJ

/-!
# `UnmarshalJSON` (arm64): entry precondition `PreJ` and the precondition of the quoted path's `UnmarshalText` call (Extracted-free)

`UnmarshalJSON` has an 80-byte frame; on the quoted path it calls `UnmarshalText(input[1:n-1])` with `SP' = SP - 80`.  `PreJ` is
`PreU` plus the facts about that inner call (its frame fits in the window, the `string(...)` requests of the substring are served,
the allocation budget covers the substring).  `preU_sub` is `PreU` of the inner call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec

namespace Fv256.Arm64.UnmarshalSpecJ

variable (C : SfdCfg)

theorem PreJ.toU {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} (h : PreJ C sb st R R2 T b L lo hi z pI nI s) (hq : ¬ Quoted s.mem pI.toNat nI.toNat) :
    PreU C sb st R R2 T b L lo hi z pI nI s := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27,
    a28, a29, a30, a31, a32, a33, a34, a35⟩, h2, -⟩ := h
  obtain ⟨o1, o2⟩ := h2 hq
  exact ⟨a1, a2, a3, a4, a5, a6, a7, o1, o2, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25,
    a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩

theorem sub_arith (p n : Nat) (h : 2 ≤ n) : p + 1 + (n - 2) ≤ p + n := by omega

theorem preU_sub {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI pI' nI' : BitVec 64} {s S : State}
    (hpre : PreJ C sb st R R2 T b L lo hi z pI nI s) (hQ : Quoted s.mem pI.toNat nI.toNat) (hn2 : 2 ≤ nI.toNat)
    (hp' : pI'.toNat = pI.toNat + 1) (hn' : nI'.toNat = nI.toNat - 2)
    (hr0 : S.regs 0 = z) (hr1 : S.regs 1 = pI') (hr2 : S.regs 2 = nI')
    (hsp : S.sp = s.sp - 80#64) (hr28 : S.regs 28 = s.regs 28)
    (hF : MemFrame s.mem S.mem [(lo, hi)]) :
    PreU C sb st R R2 T b L lo hi z pI' nI' S := by
  obtain ⟨hp0, -, hext⟩ := hpre
  obtain ⟨hlo5, hokH, hokD, hcost, hchunk⟩ := hext hQ
  have hp := hp0
  obtain ⟨-, -, -, hMod, hEnv, hlo, hhi, -, hstW, hstR, hstP, hstZ, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo,
    hMr, hMb, hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, -⟩ := hp
  have hbd : pI'.toNat + nI'.toNat ≤ 2 ^ 48 := by
    obtain ⟨-, b2⟩ := hibuf
    rw [hp', hn']; omega
  have hiw' : pI'.toNat + nI'.toNat ≤ lo ∨ hi ≤ pI'.toNat := by
    rw [hp', hn']; omega
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp' : S.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, Outside a n [(lo, hi)] → S.mem.readLE a n = s.mem.readLE a n := fun a n h => hF.readLE a n h
  have hlaws := Mod.laws C hMod
  have hpriv := Mod.priv C hMod
  have hgz : (S.regs 28).toNat = (s.regs 28).toNat := by rw [hr28]
  have hz2 := hzbuf
  have hMu2 := hMult.2.1
  simp only [outside_cons, outside_nil, and_true] at hMu2
  have hE2' := hE2
  have hE3' := hE3
  have hB2' := hB2
  have hB3' := hB3
  have hMo' := hMo
  simp only [outside_cons, outside_nil, and_true] at hE2' hE3' hB2' hB3' hMo'
  refine ⟨hr0, hr1, hr2, hMod, ?_, by omega, by omega, ?_, ?_, ?_, hstW, hstR, hstP, hstZ, ?_, hMt, ?_, ?_, hE2, hE3, ?_, hB2, hB3,
    ?_, ?_, hMo, hMr, ?_, ?_, hzwin, hzR, hzP, hzS, ?_, ?_, ?_, ?_⟩
  · -- Env
    refine ⟨by omega, by omega, e3, by omega, ?_, by rw [hgz]; exact e6, ?_, ?_, e9, e10, by rw [hgz]; exact e11,
      by rw [hgz]; exact e12, by rw [hgz]; exact e13, e14, ?_, ?_, ?_, e18⟩
    · rw [hF.accessible]; exact e5
    · rw [hgz, hF.accessible]; exact e7
    · rw [hgz, hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
    · exact StaticOK.frame e15 hF e14
    · rw [hr28]; refine hlaws.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have a1 := MemFrame.outside_mem e10 hr
      simp only [outside_cons, outside_nil, and_true] at a1 ⊢
      omega
    · rw [hgz]
      refine RtInv.inv_frame' hF (fun r hr => ?_) e17
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      left; rcases hr with rfl; exact e9
  · rw [hsp', hp', hn']; have e : s.sp.toNat - 80 - 72 = s.sp.toNat - 152 := by omega
    rw [e]; exact hokH
  · rw [hsp', hp', hn']; have e : s.sp.toNat - 80 - 40 = s.sp.toNat - 120 := by omega
    rw [e]; exact hokD
  · rw [hn']; exact hcost
  · -- MultOK
    obtain ⟨u1, u2, u3⟩ := hMult
    have u2' := u2
    simp only [outside_cons, outside_nil, and_true] at u2'
    refine ⟨by rw [hF.accessible]; exact u1, u2, ?_⟩
    intro k hk1 hk2
    obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
    have v4' := v4
    simp only [outside_cons, outside_nil, and_true] at v4'
    have hread : S.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
      hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [hread]
    refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, v4⟩
    have hv : S.mem.readLE (s.mem.readLE (C.mulTab + 8 * k) 8) 32 = s.mem.readLE (s.mem.readLE (C.mulTab + 8 * k) 8) 32 :=
      hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; exact v4'.1)
    show Janus.Spec.val256 S.mem _ = _
    unfold Janus.Spec.val256 at v3 ⊢
    rw [hv]; exact v3
  · intro k hk1 hk2
    have hread : S.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
      hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
    rw [hread]; exact hMk k hk1 hk2
  · rw [hF.accessible]; exact hE1
  · rw [hF.accessible]; exact hB1
  · -- InitDone
    obtain ⟨i1, i2, i3, i4, i5⟩ := hInit
    have o1 : ∀ a, a = C.ioEOF ∨ a = C.ioEOF + 8 → S.mem.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha; exact hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; rcases ha with rfl | rfl <;> omega)
    have o2 : ∀ a, a = C.errBig ∨ a = C.errBig + 8 → S.mem.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha; exact hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; rcases ha with rfl | rfl <;> omega)
    exact ⟨by rw [o1 _ (Or.inl rfl)]; exact i1, by rw [o1 _ (Or.inr rfl)]; exact i2, by rw [o2 _ (Or.inl rfl)]; exact i3,
      by rw [o2 _ (Or.inr rfl)]; exact i4, i5⟩
  · rw [hF.accessible]; exact hMa
  · intro k hk
    rw [hrd _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hMb k hk
  · obtain ⟨b1, b2⟩ := hzbuf
    exact ⟨by rw [hF.accessible]; exact b1, b2⟩
  · rw [hgz]; exact hzg
  · obtain ⟨b1, b2⟩ := hibuf
    refine ⟨?_, hbd⟩
    rw [hF.accessible]
    rw [hp', hn']
    exact Janus.Arm64.Memory.accessible_sub s.mem b1 (Or.inl rfl) (Nat.le_succ _) (sub_arith _ _ hn2)
  · exact hiw'
  · intro sl h1 h2 h3
    rw [hn'] at h3
    have := hchunk sl h1 h2 h3
    rw [hn']; exact this

end Fv256.Arm64.UnmarshalSpecJ
