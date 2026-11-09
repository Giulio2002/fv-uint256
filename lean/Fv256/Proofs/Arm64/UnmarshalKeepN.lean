import Fv256.Proofs.Arm64.UnmarshalHexN

/-!
# Frame-keeping facts for the nested `UnmarshalText` call (arm64, Extracted-free)

The two words at `SP` and `SP - 8` (the caller's saved `X30`/`X29` slots, when `UnmarshalText` is called from `UnmarshalJSON`) are
untouched by the whole `UnmarshalText` call: they lie in no frame of `string(input)`, of `SetFromDecimal` or of `fromHex`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalDecN Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalHex

namespace Fv256.Arm64.UnmarshalKeepN

variable (C : SfdCfg)

theorem topPost_frame {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {S3 s' : State} (hq : TopPost C R R2 T b L lo hi z pS nS S3 s') :
    MemFrame S3.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) := by
  obtain ⟨-, -, -, -, -, -, hcases⟩ := hq
  rcases hcases with ⟨v, hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c1, cTe, cMF⟩
  · exact cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2)
  · exact cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2)
  · exact cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2)
  · exact cMF

theorem dec_keep {sp : Nat} {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 s' : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {v29 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (hsp0 : s.sp.toNat = sp)
    (hP : SbPost R st b L sp s pI nI r0 r1 M0 m (sp - 40))
    (hM0c : M0 = (((s.mem.writeLE (sp - 112) 8 ra).writeLE (sp - 120) 8 v29).writeLE (sp + 16) 8 pI.toNat).writeLE
      (sp + 8) 8 z.toNat)
    (hS3 : S3.mem = m)
    (hq : TopPost C R R2 T (b - roundupsize nI.toNat true)
      (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)])) lo (sp - 40) z r0 nI S3 s') :
    s'.mem.readLE sp 8 = s.mem.readLE sp 8 ∧ s'.mem.readLE (sp - 8) 8 = s.mem.readLE (sp - 8) 8 := by
  subst hsp0
  have hcF := topPost_frame C hq
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hzw := hp.zwin
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hp.env
  obtain ⟨hMF, -, -, -, -⟩ := hP
  have hne : s.sp.toNat - 40 ≠ 0 := by omega
  rw [if_neg hne] at hMF
  have key : ∀ a, (a = s.sp.toNat ∨ a = s.sp.toNat - 8) → s'.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    rw [hcF.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, ?_, ?_⟩ <;> omega), hS3,
      hMF.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega), hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

theorem hex_keep {sp : Nat} {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 s' : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {v29 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s) (hsp0 : s.sp.toNat = sp)
    (hP : SbPost R st b L sp s pI nI r0 r1 M0 m (sp - 72))
    (hM0c : M0 = (((s.mem.writeLE (sp - 112) 8 ra).writeLE (sp - 120) 8 v29).writeLE (sp + 16) 8 pI.toNat).writeLE
      (sp + 8) 8 z.toNat)
    (hsp3 : S3.sp = s.sp - 112#64) (hS3 : S3.mem = m)
    (hq : FromHexPost z r0 nI S3 s') :
    s'.mem.readLE sp 8 = s.mem.readLE sp 8 ∧ s'.mem.readLE (sp - 8) 8 = s.mem.readLE (sp - 8) 8 := by
  subst hsp0
  obtain ⟨-, -, -, -, -, -, cMF, -, -⟩ := hq
  have hlo0 := hpre.toS.lo4
  have hsp : S3.sp.toNat = s.sp.toNat - 112 := by
    rw [hsp3]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [hsp] at cMF
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hzw := hp.zwin
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hp.env
  obtain ⟨hMF, -, -, -, -⟩ := hP
  have hne : s.sp.toNat - 72 ≠ 0 := by omega
  rw [if_neg hne] at hMF
  have key : ∀ a, (a = s.sp.toNat ∨ a = s.sp.toNat - 8) → s'.mem.readLE a 8 = s.mem.readLE a 8 := by
    intro a ha
    rw [cMF.readLE a 8 (by
      simp only [outside_cons, outside_nil, and_true]
      refine ⟨?_, ?_, ?_⟩ <;> omega), hS3,
      hMF.readLE a 8 (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega), hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  exact ⟨key _ (Or.inl rfl), key _ (Or.inr rfl)⟩

end Fv256.Arm64.UnmarshalKeepN
