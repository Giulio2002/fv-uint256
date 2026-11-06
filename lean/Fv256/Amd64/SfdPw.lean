import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdEnv
import Fv256.Amd64.SfdTePre
import Fv256.Amd64.SfdBridge
import Fv256.Amd64.SfdParse
import Fv256.Amd64.SfdToErrorX

/-!
# `strconv.ParseUint(s, 10, 64)` (the exported wrapper) on a chunk of 1 to 19 bytes (amd64)

The wrapper calls `internal/strconv.ParseUint` (`SfdParse.pu_sum`) and, on a failure, `strconv.toError` (the summary
`hte`, a hypothesis here and discharged where this lemma is used).  Result registers: `RAX = n`, `RBX, RCX = err`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdParse Fv256.I

namespace Fv256.Amd64.SfdPw

abbrev pw : Nat := segAddr Extracted.program "strconv.ParseUint"
abbrev fnStr : Nat := Extracted.dataAddr.«.rodata#3d2a826c»

open Fv256.C in
def PwPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = p ∧ s.regs 3 = len ∧ s.regs 1 = 10#64 ∧ s.regs 7 = 64#64 ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 19 ∧
  Mod R R2 T L ∧ Env R R2 T b L lo hi s ∧ lo + 4280 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 48 ≤ hi ∧
  ChunkOK R R2 L b p len lo hi s.mem

open Fv256.C in
def PwPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧
  ((allDec (bytesAt s.mem p.toNat) 0 len.toNat ∧ (s'.regs 0).toNat = decSum (bytesAt s.mem p.toNat) 0 len.toNat ∧
      s'.regs 3 = 0 ∧ s'.regs 1 = 0 ∧ Env R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat + 40)]) ∨
   (¬ allDec (bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 0 = 0 ∧
      (∃ (q : Nat) (t : BitVec 64), s'.regs 3 = BitVec.ofNat 64 numErrItab ∧ s'.regs 1 = t ∧
        TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 p len s s' q t.toNat) ∧
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])))


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pw_sum (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (p len : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (Extracted.program.link impl) pw (PwPre R R2 T b L lo hi p len) (PwPost R R2 T b L lo hi p len) := by
  intro s hpc ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, hl1, hl2, hMod, hEnv, hlo, hhi, hCh⟩
  have hte := te_sum impl R R2 hMod.1 T b L (BitVec.ofNat 64 fnStr) 9#64 p len hif hnew hmg hmv hwb1 hwb2
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  obtain ⟨hch1, hch2, hch3, hch4, hch5, hch6, hch7, hch8⟩ := hCh
  janus64_run until [ip]
  refine reach_name ?_
  intro S1 hS1
  have hrsp1 : (S1.regs 4).toNat = (s.regs 4).toNat - 88 := by
    subst hS1; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; rw [BitVec.toNat_sub]; simp; omega
  have hSf : MemFrame s.mem S1.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat + 40)] := by
    subst hS1; dsimp only; janus_frame
  have hret1 : S1.mem.readLE (S1.regs 4).toNat 8 = 4771367 := by
    rw [hrsp1]; subst hS1; dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
  have hSacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := hSf.accessible
  have hbytes : ∀ k, k < len.toNat → Fv256.C.bytesAt S1.mem p.toNat k = Fv256.C.bytesAt s.mem p.toNat k := by
    intro k hk
    unfold Fv256.C.bytesAt
    exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hg1 : S1.regs 14 = s.regs 14 := by subst hS1; simp [setRegF_apply]
  have hSg : S1.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hS0 : S1.regs 0 = p := by subst hS1; simp [setRegF_apply, h0]
  have hS3 : S1.regs 3 = len := by subst hS1; simp [setRegF_apply, h3]
  have hS1' : S1.regs 1 = 10#64 := by subst hS1; simp [setRegF_apply, h1]
  have hS7 : S1.regs 7 = 64#64 := by subst hS1; simp [setRegF_apply, h7]
  refine ReachesRet.call (pu_sum impl p len) (by subst hS1; rfl)
    ⟨⟨by rw [hSacc, hrsp1]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega) |> fun h => Arm64.Memory.accessible_weaken _ h,
      by rw [hret1]; omega, by subst hS1; simpa using hx15, by subst hS1; simpa using hdf⟩,
      hS0, hS3, hS1', hS7, ⟨hch5, by rw [hSacc]; exact hch4⟩, hl1, hl2,
      ⟨by simp only [regG, stackguard0Offset, hg1]; omega, by simp only [regG, stackguard0Offset, hg1]; rw [hSacc]; exact e7, by
        simp only [stackguard0, regG, regSP, stackguard0Offset, hg1]; rw [hSg]; omega⟩,
      ⟨by simp only [regSP]; omega, by simp only [regSP]; omega, by simp only [regSP]; rw [hSacc, hrsp1]; exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)⟩,
      by rw [hrsp1]; omega⟩ ?cont
  case cont =>
    intro s' hpc' ⟨⟨k1, k2, k3, k4, k5, k6, k7⟩, hfr, hcase⟩
    have hra : retAddrOf S1 = BitVec.ofNat 64 4771367 := by simp only [retAddrOf, hret1]
    rw [hra] at k1
    rcases hcase with ⟨hA, hv, hz3, hz1⟩ | ⟨hA, hz0, hz3, hz1⟩
    · subst hS1
      have hrsp' : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
        rw [BitVec.toNat_sub]; simp; omega
      simp only [calleeStack, setRegF_apply, reduceIte, Nat.reduceEqDiff, hrsp'] at hfr
      have hfinT : MemFrame s.mem s'.mem [((s.regs 4).toNat - 96, (s.regs 4).toNat + 40)] := hSf.trans hfr (by
        intro a n h
        simp only [outside_cons, outside_nil, and_true] at h ⊢
        omega)
      have hfinF : MemFrame s.mem s'.mem [(lo, hi)] := hfinT.mono (by
        intro a n h
        simp only [outside_cons, outside_nil, and_true] at h ⊢
        omega)
      janus64_run
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ⟨?_, ?_, ?_, ?_, ?_, hfinT⟩⟩
      · simp only [retAddrOf]
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · simp [setRegF_apply, k4]
      · simpa using k5
      · simpa using hdf
      · simpa using k7
      · intro k a b
        have := hA k a b
        rwa [hbytes k b] at this
      · simp [setRegF_apply]
        rw [hv]
        exact decSum_congr _ _ 0 _ (fun k _ hk => hbytes k (by omega))
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · refine Env.frame0 hMod.1 hEnv ?_ ?_ hfinF (by omega)
        · simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
          rw [BitVec.toNat_add]; simp; omega
        · simp [setRegF_apply, k4]
    · subst hS1
      have hrsp' : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
        rw [BitVec.toNat_sub]; simp; omega
      simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hrsp'] at hfr
      have hfinF : MemFrame s.mem s'.mem [(lo, hi)] := hSf.trans hfr (by
        intro a n h
        simp only [outside_cons, outside_nil, and_true] at h ⊢
        omega)
      have hz3n : (s'.regs 3).toNat = 5183968 := by rw [hz3]; decide
      janus64_run until [te]
      refine reach_name ?_
      intro S2 hS2
      have hrsp2 : (S2.regs 4).toNat = (s.regs 4).toNat - 88 := by
        subst hS2; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]; rw [BitVec.toNat_sub]; simp; omega
      have hfr2 : MemFrame s'.mem S2.mem [((s.regs 4).toNat - 88, (s.regs 4).toNat)] := by
        subst hS2; dsimp only; janus_frame
      have hSF : MemFrame s.mem S2.mem [(lo, hi)] := hfinF.trans hfr2 (by
        intro a n h
        simp only [outside_cons, outside_nil, and_true] at h ⊢
        omega)
      have hrg2 : S2.regs 14 = s.regs 14 := by subst hS2; simp [setRegF_apply, k4]
      have hEnv2 : Env R R2 T b L lo hi S2 :=
        Env.frame0 hMod.1 hEnv (by rw [hrsp2]; refine ⟨by omega, by omega, by omega⟩) hrg2 hSF (by omega)
      have hEnv3 : Env R R2 T b L ((S2.regs 4).toNat - 4192) ((S2.regs 4).toNat + 72) S2 :=
        Env.shrink hEnv2 (by omega) (by omega) (by omega) (by omega)
      have hret2 : S2.mem.readLE (S2.regs 4).toNat 8 = 4771420 := by
        rw [hrsp2]; subst hS2; dsimp only
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
      have hS2acc : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := hSF.accessible
      have hr0 : S2.regs 0 = BitVec.ofNat 64 fnStr := by subst hS2; simp [setRegF_apply]; decide
      have hr3 : S2.regs 3 = 9#64 := by subst hS2; simp [setRegF_apply]
      have hr1 : S2.regs 1 = p := by subst hS2; simp [setRegF_apply]
      have hr7 : S2.regs 7 = len := by subst hS2; simp [setRegF_apply]
      have hr9 : S2.regs 9 = BitVec.ofNat 64 SfdEnv.errItab := by
        subst hS2; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
        apply BitVec.eq_of_toNat_eq; rw [hz3]; simp only [BitVec.toNat_ofNat]; decide
      have hr10 : S2.regs 10 = BitVec.ofNat 64 synConst := by
        subst hS2; simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff]
        apply BitVec.eq_of_toNat_eq; rw [hz1]; simp only [BitVec.toNat_ofNat]; decide
      refine ReachesRet.call hte (by subst hS2; rfl) (tePre_of_pre' ⟨⟨?_, ?_, ?_, ?_⟩, hr0, hr3, hr1, hr7, hr9, hr10, hl1,
        by omega, by omega, hMod, hEnv3, hch1, hch2, hch3, ?_, hch5, ?_, hch7, hch8⟩) ?cont2
      · rw [hS2acc, hrsp2]; exact Arm64.Memory.accessible_weaken _ (Arm64.Memory.accessible_mono _ e5 (by omega) (by omega))
      · rw [hret2]; omega
      · subst hS2; simpa [k5] using hx15
      · subst hS2; simpa [k6] using hdf
      · rw [hS2acc]; exact hch4
      · rw [hrsp2]; omega
      case cont2 =>
        intro s3 hpc3 ⟨⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨q, t, hr0', hr3', hobj⟩, hfr3⟩
        have hra2 : retAddrOf S2 = BitVec.ofNat 64 4771420 := by simp only [retAddrOf, hret2]
        rw [hra2] at c1
        subst hS2
        have hrsp'' : (s.regs 4 - 88#64).toNat = (s.regs 4).toNat - 88 := by
          rw [BitVec.toNat_sub]; simp; omega
        simp only [setRegF_apply, reduceIte, Nat.reduceEqDiff, hrsp'', List.append_assoc] at hfr3
        have hO1 : Outside ((s.regs 4).toNat - 16) 24 R.rt := Outside.of_sub e9 (by omega) (by omega)
        have hO2 : Outside ((s.regs 4).toNat - 16) 24 R2.priv := Outside.of_sub e10 (by omega) (by omega)
        janus64_run
        have oE := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
        simp only [Nat.add_sub_cancel_left] at oE
        obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := hobj
        have hobj' : TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 p len s s3 q t.toNat := by
          refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, ?_, ?_, ?_⟩
          · rw [o9]; exact hSF.readLE _ _ (Outside.of_sub oE (by omega) (by omega))
          · rw [o10]; exact hSF.readLE _ _ (Outside.of_sub oE (by omega) (by omega))
          · intro k hk
            rw [o11 k hk]
            exact hSF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
          · simpa [setRegF_apply, c4, k4] using o12
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr ⟨?_, ?_, ⟨q, t, ?_, ?_, hobj'⟩, ?_⟩⟩
        · simp only [retAddrOf]
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · simp [setRegF_apply, c4, k4]
        · simp [c5, k5, hx15]
        · simp [c6, k6, hdf]
        · simpa [k7] using c7
        · intro h
          apply hA
          intro k a b
          rw [hbytes k b]
          exact h k a b
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · exact hSF.trans hfr3 (by
            intro a n h
            simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
            obtain ⟨⟨h1, h2⟩, h3⟩ := h
            exact ⟨h3, h1, h2, by omega⟩)

end Fv256.Amd64.SfdPw
