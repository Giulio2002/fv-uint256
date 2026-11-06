import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC

/-!
# `FromDecimal` (amd64): precondition and the `SetFromDecimal` call-site lemma (Extracted-free)

`PreC`: the model facts of `SfdTopSpec.TopPre` minus the receiver `z` (which `newobject` allocates inside the proof).
`toppre_of_call`: from `PreC` at the entry state and the facts of the state at the `SetFromDecimal` call (the object `z` that
`newobject` returned, the memory frame, the runtime invariant after the allocation), `TopPre` for that call.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.FromDecimalSpec

variable (C : SfdCfg)

theorem outside_of_in {rt : List (Nat × Nat)} {z n : Nat} (hz : InRanges z n rt) :
    ∀ rs : List (Nat × Nat), (∀ r ∈ rs, r.1 ≤ r.2) → (∀ r ∈ rs, Outside r.1 (r.2 - r.1) rt) → Outside z n rs := by
  intro rs
  induction rs with
  | nil => intros; trivial
  | cons r rs ih =>
    intro hw ho
    obtain ⟨a, b⟩ := r
    simp only [outside_cons]
    refine ⟨?_, ih (fun r hr => hw r (List.mem_cons_of_mem _ hr)) (fun r hr => ho r (List.mem_cons_of_mem _ hr))⟩
    obtain ⟨q, hq, h1, h2⟩ := hz
    have hab := hw (a, b) (List.mem_cons_self ..)
    have := MemFrame.outside_mem (ho (a, b) (List.mem_cons_self ..)) hq
    simp only at hab this
    omega

def PreC (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi tI : Nat) (pS nS : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = pS ∧ s.regs 3 = nS ∧ Mod C R R2 T L ∧
  Env C R R2 T b L lo hi s ∧ lo + 4848 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 24 ≤ hi ∧
  R.ok C.newobject [tI] ∧ blockSize 32 true ≤ b ∧
  MultOK C lo lo hi s.mem ∧ Outside C.mulTab 40 R.rt ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  s.mem.accessible C.ioEOF 16 false = true ∧ Outside C.ioEOF 16 [(lo, hi)] ∧ Outside C.ioEOF 16 R.rt ∧
  s.mem.accessible C.errBig 16 false = true ∧ Outside C.errBig 16 [(lo, hi)] ∧ Outside C.errBig 16 R.rt ∧
  Buffer s pS nS.toNat false ∧ (pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (Outside pS.toNat nS.toNat R.rt ∨ InRanges pS.toNat nS.toNat L) ∧ (∀ r ∈ R2.priv, r.1 ≤ r.2) ∧
  ChunkAll C R R2 L (b - blockSize 32 true) pS.toNat nS.toNat lo hi s.mem

theorem outside_sub_stack (rt : List (Nat × Nat)) (lo hi sp a n : Nat) (hlo : lo + 4848 ≤ sp) (hhi : sp + 24 ≤ hi)
    (h : Outside a n (rt ++ [(lo, hi)])) :
    Outside a n [(lo, hi)] ∧ Outside a n (rt ++ [(sp - 48 - 4096, sp - 48), (sp - 48 + 8, sp - 48 + 8 + 8)]) := by
  simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨h2, h1, by omega, by omega⟩

theorem chunkOK_mono {R : RtInv} {R2 : IfaceModel} {L L' : List (Nat × Nat)} {b : Nat} {sp sl : BitVec 64} {lo hi : Nat}
    {m m' : Janus.Arm64.Memory} (h : ChunkOK C R R2 L b sp sl lo hi m) (hL : ∀ r ∈ L, r ∈ L')
    (hacc : m'.accessible sp.toNat sl.toNat false = true) : ChunkOK C R R2 L' b sp sl lo hi m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, hacc, h5, h6, h7.elim Or.inl (fun hi => Or.inr (hi.of_subset hL)), h8⟩

theorem toppre_of_call {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi tI : Nat}
    {pS nS zv : BitVec 64} {s S3 : State}
    (hpre : PreC C R R2 T b L lo hi tI pS nS s)
    (hr0 : S3.regs 0 = zv) (hr3 : S3.regs 3 = pS) (hr1 : S3.regs 1 = nS) (hr4 : S3.regs 4 = s.regs 4 - 48#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hret : S3.mem.readLE ((s.regs 4).toNat - 48) 8 < 2 ^ 47)
    (hF : MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]))
    (hz : InRanges zv.toNat 32 R.rt) (hzL : ApartAll zv.toNat 32 L) (hza : s.mem.accessible zv.toNat 32 true = true) (hz48 : zv.toNat + 32 ≤ 2 ^ 48)
    (hInv : R.inv (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) (S3.regs 14).toNat
      (view R.rt (L ++ [(zv.toNat, zv.toNat + 32)]) S3.mem)) :
    TopPre C R R2 T (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) lo hi zv pS nS S3 := by
  obtain ⟨hRet, h0, h3, hMod, hEnv, hlo, hhi, hok, hbud, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hBuf, hPS, hPR, hPW, hCh⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : (S3.regs 4).toNat = (s.regs 4).toNat - 48 := by
    rw [hr4]; have := (s.regs 4).isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hspS : 48 ≤ (s.regs 4).toNat := by omega
  have hrt : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n := by
    intro a n h1 h2
    exact hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hMod' := hMod
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ := hMod'
  have hzP : Outside zv.toNat 32 R2.priv := outside_of_in hz _ hPW m4
  have hzS : ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(zv.toNat, zv.toNat + 32)] := by
    intro r hr
    have h2 := InRanges.apart hz (b := r.1) (k := r.2 - r.1) (m7 r hr)
    simp only [outside_cons, outside_nil, and_true]
    unfold Apart at h2; omega
  have hLs : ∀ r ∈ L, r ∈ L ++ [(zv.toNat, zv.toNat + 32)] := fun r hr => List.mem_append_left _ hr
  have hw1 : (Janus.Arm64.Memory.accessible s.mem ((s.regs 4).toNat - 48) 8 false = true) :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
  have hWinZ : Apart lo (hi - lo) zv.toNat 32 := InRanges.apart hz e9
  have hGZ : Apart ((s.regs 14).toNat + 16) 8 zv.toNat 32 := InRanges.apart hz e11
  unfold TopPre
  refine ⟨?_, hr0, hr3, hr1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold RetOK
    rw [hsp, hF.accessible]
    exact ⟨hw1, hret, hx15, hdf⟩
  · -- Mod
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, m8, m9, m10, m11⟩
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact m5 r h
    · simp only [List.mem_singleton] at h; subst h; simpa using hzP
  · -- Env
    have hgz : (S3.regs 14).toNat = (s.regs 14).toNat := by rw [hr14]
    refine ⟨by omega, by omega, e3, by omega, ?_, by rw [hgz]; exact e6, ?_, ?_, e9, e10, by rw [hgz]; exact e11,
      by rw [hgz]; exact e12, by rw [hgz]; exact e13, e14, ?_, ?_, hInv, ?_⟩
    · rw [hF.accessible]; exact e5
    · rw [hgz, hF.accessible]; exact e7
    · rw [hgz, hrt _ _ e11 (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact e8
    · refine StaticOK.frame e15 hF ?_
      intro r hr
      rw [outside_append]
      refine ⟨m7 r hr, ?_⟩
      have := e14 r hr
      exact this
    · rw [hr14]; refine m1.env_frame _ _ _ e16 (Janus.Spec.Map.Agrees.of_memFrame hF ?_)
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have a1 := MemFrame.outside_mem e10 hr
      have a2 : Outside a 1 R.rt := Outside.of_sub (m4 r hr) h1 (by omega)
      rw [outside_append]
      refine ⟨a2, ?_⟩
      simp only [outside_cons, outside_nil, and_true]
      omega
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact e18 r h
      · simp only [List.mem_singleton] at h; subst h
        simp only [outside_cons, outside_nil, and_true]
        unfold Apart at hWinZ; omega
  · omega
  · omega
  · -- MultOK
    obtain ⟨u1, u2, u3⟩ := hMult
    have u2' := u2
    simp only [outside_cons, outside_nil, and_true] at u2'
    refine ⟨by rw [hF.accessible]; exact u1, ?_, ?_⟩
    · have := InRanges.apart hz hMt
      simp only [outside_cons, outside_nil, and_true]
      unfold Apart at this
      exact ⟨u2'.1, by omega⟩
    · intro k hk1 hk2
      obtain ⟨v1, v2, v3, v4⟩ := u3 k hk1 hk2
      have v4' := v4
      simp only [outside_cons, outside_nil, and_true] at v4'
      have hread : S3.mem.readLE (C.mulTab + 8 * k) 8 = s.mem.readLE (C.mulTab + 8 * k) 8 :=
        hrt _ _ (Outside.of_sub hMt (by omega) (by omega))
          (by simp only [outside_cons, outside_nil, and_true]; omega)
      rw [hread]
      have hMk' := hMk k hk1 hk2
      generalize s.mem.readLE (C.mulTab + 8 * k) 8 = pp at *
      refine ⟨by rw [hF.accessible]; exact v1, v2, ?_, ?_⟩
      · have hv : S3.mem.readLE pp 32 = s.mem.readLE pp 32 :=
          hrt pp 32 hMk' (by simp only [outside_cons, outside_nil, and_true]; exact v4'.1)
        show S3.mem.readLE pp 32 = _
        rw [hv]
        exact v3
      · have := InRanges.apart hz hMk'
        unfold Apart at this
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨v4'.1, by omega⟩
  · -- ioEOF
    rw [hF.accessible]; exact hE1
  · have := InRanges.apart hz hE3
    unfold Apart at this
    simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
    exact ⟨hE2, by omega⟩
  · rw [hF.accessible]; exact hB1
  · have := InRanges.apart hz hB3
    unfold Apart at this
    simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
    exact ⟨hB2, by omega⟩
  · -- Buffer z
    exact ⟨hz48, by rw [hF.accessible]; exact hza⟩
  · unfold Apart at hWinZ; omega
  · exact Or.inr ⟨(zv.toNat, zv.toNat + 32), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
  · exact hzP
  · exact hzS
  · rw [hr14]; unfold Apart at hGZ; omega
  · -- Buffer pS
    obtain ⟨b1, b2⟩ := hBuf
    exact ⟨b1, by rw [hF.accessible]; exact b2⟩
  · exact hPS
  · rcases hPR with h | h
    · have := InRanges.apart hz h
      unfold Apart at this; omega
    · have := hzL.apart_of_inRanges h
      omega
  · -- ChunkAll
    intro sp sl h1 h2 h3 h4
    have := hCh sp sl h1 h2 h3 h4
    refine chunkOK_mono C this (fun r hr => List.mem_append_left _ hr) ?_
    rw [hF.accessible]; exact this.2.2.2.1

end Fv256.Amd64.FromDecimalSpec