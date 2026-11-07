import Fv256.Arm64.ScanByt0
import Fv256.Arm64.ScanCall

/-!
# `Scan` (arm64), the `[]byte` case: the entry facts of `scanScientificFromString` for the copy (Extracted-free)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSpec Fv256.Arm64.ScanCall Fv256.Arm64.ScanByt0

namespace Fv256.Arm64.ScanByt1

variable (C : SfdCfg)

set_option maxRecDepth 100000 in
theorem pr_sub {m : Janus.Arm64.Memory} {p n p' n' : Nat} (h : Fv256.IndexByte.PageReadable m p n) (h1 : p ≤ p')
    (h2 : p' + n' ≤ p + n) : Fv256.IndexByte.PageReadable m p' n' := by
  unfold Fv256.IndexByte.PageReadable at *
  by_cases hn' : n' = 0
  · exact Or.inl hn'
  · right
    rcases h with h | ⟨h3, h4⟩
    · omega
    · refine ⟨by omega, Janus.Arm64.Memory.accessible_sub _ h4 (Or.inl rfl) (by omega) (by omega)⟩

set_option maxRecDepth 100000 in
/-- the copy is page-readable: it lives in the runtime's heap, on the stack buffer, or in `staticuint64s` -/
theorem byt_pages {R : RtInv} {st lo hi pI r0 n : Nat} {s S1 S2 : State} {W : List (Nat × Nat)}
    (hpg : PagesB R st lo hi s.mem) (hF : MemFrame s.mem S2.mem W)
    (hSA : StrAt R.rt (s.sp.toNat - 40) st pI n r0 S1.mem) (hlo : lo ≤ s.sp.toNat - 40) (hhi : s.sp.toNat - 8 ≤ hi)
    (hbyte : S1.mem.readLE pI 1 < 256) :
    Fv256.IndexByte.PageReadable S2.mem r0 n := by
  refine pr_frame_n hF ?_
  obtain ⟨p1, p2, p3⟩ := hpg
  rcases hSA with h0 | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, r, hr, hr1, hr2⟩
  · exact Or.inl h0
  · subst h2
    exact pr_sub p3 (by omega) (by omega)
  · subst h4
    exact pr_sub p1 (by omega) (by omega)
  · exact pr_sub (p2 r hr) hr1 (by omega)


set_option maxRecDepth 100000 in
/-- everything `sci_summary` needs at the call, for the copy -/
theorem byt_pre0 {p : Janus.Program} {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI r0 r1 : BitVec 64} {s S1 S2 : State}
    (hpre : PreB C sb st R R2 T b L lo hi z pI nI s) (hpg : PagesB R st lo hi s.mem)
    (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hF1 : MemFrame s.mem S1.mem [(lo, hi)]) (hdl1 : p.DataLoaded S1.mem) (hreg2 : S2.mem.regions = S1.mem.regions)
    (hmf : MemFrame S1.mem S2.mem (R.rt ++ [(s.sp.toNat - 80 - 4096, s.sp.toNat - 80 - 8),
      (s.sp.toNat - 80 + 8, s.sp.toNat - 80 + 8 + 24)] ++
      if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hsoa : (r1.toNat = (strBytes S1.mem pI.toNat nI.toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
        (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
        strBytes S2.mem r0.toNat r1.toNat = strBytes S1.mem pI.toNat nI.toNat) ∧
      StrAt R.rt (s.sp.toNat - 40) st pI.toNat r1.toNat r0.toNat S1.mem)
    (hlf : LiveFrame S1.mem S2.mem L (if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hfr : FreshFrom (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L)
    (hinv : R.inv (b - roundupsize nI.toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 28).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) S2.mem))
    (hr0 : S2.regs 0 = z) (hr1 : S2.regs 1 = r0) (hr2 : S2.regs 2 = r1) (hsp2 : S2.sp = s.sp - 80#64)
    (hr28 : S2.regs 28 = s.regs 28) (h30a : (S2.regs 30).toNat % 4 = 0) (h30b : (S2.regs 30).toNat < 2 ^ 48) :
    (SciPre C R R2 T (b - roundupsize nI.toNat true) (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]))
      lo (s.sp.toNat - 40) z r0 nI S2 ∧ InitDone C R2 S2.mem ∧ p.DataLoaded S2.mem) ∧
    (∀ k, k < nI.toNat → S2.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1) ∧
    MemFrame s.mem S2.mem (R.rt ++ [(lo, hi)]) := by
  have hcall := byt_call_pre C hpre hlo hhi hF1 hmf hsoa hlf hfr hinv hr0 hr1 hr2 hsp2 hr28
  obtain ⟨htop, hbytes, hF⟩ := hcall
  have hpre' := hpre
  obtain ⟨hMod, hEnv, hok, hcost, hstW, hstR, hstP, hstZ, hMult, hMt, hMk, hE1, hE2, hE3, hB1, hB2, hB3, hInit, hMa, hMo, hMr, hMb,
    hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hRW, hchunk⟩ := hpre'
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hsp : S2.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp2]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hn : r1.toNat = nI.toNat := by rw [hsoa.1.1]; simp
  have hbne : s.sp.toNat - 40 ≠ 0 := by omega
  refine ⟨⟨⟨TopPre0.toTop C h30a h30b htop, by omega, ?_⟩, ?_, ?_⟩, hbytes, hF⟩
  · have hmf' := hmf
    rw [if_neg hbne] at hmf'
    rw [hn] at hsoa
    exact byt_pages hpg (hF.mono (fun a n h => h)) hsoa.2 (by omega) (by omega) (by simpa using Janus.Arm64.Memory.readLE_lt S1.mem pI.toNat 1)
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hInit
    have o1 : Outside C.ioEOF 16 (R.rt ++ [(lo, hi)]) := by simp only [outside_append, outside_cons, outside_nil, and_true] at hE2 hE3 ⊢; exact ⟨hE3, hE2.1⟩
    have o2 : Outside C.errBig 16 (R.rt ++ [(lo, hi)]) := by simp only [outside_append, outside_cons, outside_nil, and_true] at hB2 hB3 ⊢; exact ⟨hB3, hB2.1⟩
    have r1' := hF.readLE C.ioEOF 8 (Outside.of_sub o1 (Nat.le_refl _) (by omega))
    have r2' := hF.readLE (C.ioEOF + 8) 8 (Outside.of_sub o1 (by omega) (by omega))
    have r3' := hF.readLE C.errBig 8 (Outside.of_sub o2 (Nat.le_refl _) (by omega))
    have r4' := hF.readLE (C.errBig + 8) 8 (Outside.of_sub o2 (by omega) (by omega))
    exact ⟨by rw [r1']; exact i1, by rw [r2']; exact i2, by rw [r3']; exact i3, by rw [r4']; exact i4, i5⟩
  · rw [if_neg hbne] at hmf
    refine dl_frame hdl1 hmf hreg2 (fun r hr => ?_)
    have hw : ∀ a n, lo ≤ a → a + n ≤ hi → S1.mem.accessible a n true = true := fun a n h1 h2 => by
      rw [hF1.accessible]; exact Janus.Arm64.Memory.accessible_sub _ e5 (Or.inr rfl) (by omega) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (hr | rfl | rfl) | rfl
    · rw [hF1.accessible]; exact hRW r hr
    · exact hw _ _ (by omega) (by omega)
    · exact hw _ _ (by omega) (by omega)
    · exact hw _ _ (by omega) (by omega)

end Fv256.Arm64.ScanByt1
