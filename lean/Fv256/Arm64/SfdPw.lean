import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdProg
import Fv256.Arm64.SfdEnv
import Fv256.Arm64.SfdToError
import Fv256.Arm64.SfdParse

/-!
# `strconv.ParseUint(s, 10, 64)` (the exported wrapper) on a chunk of 1 to 19 bytes (arm64): STATEMENT

`pw_sum` is proved (over te_sum); consumers may use `PwSum`.
Registers: in `X0 = p, X1 = len, X2 = 10, X3 = 64`; out `X0 = n`, `X1, X2 = err` (ok: `X1 = X2 = 0`).
Window `[lo, hi)`: the function's whole stack window (`Env R R2 T b L lo hi`), `lo + 4288 <= SP`, `SP + 48 <= hi`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError

namespace Fv256.Arm64.SfdPw

abbrev pw : Nat := segAddr Fv256.Arm64.SfdProg.program "strconv.ParseUint"
abbrev fnStr : Nat := 0xeb483

def PwPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
  s.regs 0 = p ∧ s.regs 1 = len ∧ s.regs 2 = 10#64 ∧ s.regs 3 = 64#64 ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 19 ∧
  Mod R R2 T L ∧ Env R R2 T b L lo hi s ∧ lo + 4288 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ hi ∧
  ChunkOK R R2 L b p len lo hi s.mem

def PwPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  s'.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ s'.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 ∧
  ((allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧
      s'.regs 1 = 0 ∧ s'.regs 2 = 0 ∧ Env R R2 T b L lo hi s' ∧ MemFrame s.mem s'.mem [(lo, hi)]) ∨
   (¬ allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 0 = 0 ∧
      (∃ (q : Nat) (t : BitVec 64), s'.regs 1 = BitVec.ofNat 64 numErrItab ∧ s'.regs 2 = t ∧
        TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 p len s s' q t.toNat) ∧
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])))

/-- the statement consumers assume (the hypotheses are the runtime contracts of the library program) -/
def PwSum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (p len : BitVec 64) : Prop :=
  Summary (P.link impl) pw (PwPre R R2 T b L lo hi p len) (PwPost R R2 T b L lo hi p len)

theorem reach_name2 {p : Program} {ret : BitVec 64} {S : State} {Q : State → Prop}
    (h : ∀ S', S' = S → ReachesRet p ret S' Q) : ReachesRet p ret S Q := h S rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem pw_sum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (p len : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    PwSum impl R R2 T b L lo hi p len := by
  intro s hpc ⟨hl1, hl2, h0, h1, h2, h3, hlen1, hlen2, hMod, hEnv, hlo, hhi, hCh⟩
  have hte := te_sum impl R R2 hMod.1 T b L (BitVec.ofNat 64 fnStr) 9#64 p len hif hnew hmg hmv hwb1 hwb2
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  obtain ⟨hch1, hch2, hch3, hch4, hch5, hch6, hch7, hch8⟩ := hCh
  janus_run until [Fv256.Arm64.SfdParse.ip]
  refine reach_name2 ?_
  intro S1 hS1
  have hlo' : lo ≤ s.sp.toNat - 4288 := by omega
  have hS1sp : S1.sp.toNat = s.sp.toNat - 96 := by subst hS1; exact arith_sp _ (by omega) _ rfl
  have hSf : MemFrame s.mem S1.mem [(s.sp.toNat - 104, s.sp.toNat + 40)] := by
    subst hS1; dsimp only; janus_frame
  have hSacc : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := hSf.accessible
  have hS30 : S1.regs 30 = 618508#64 := by subst hS1; simp [setReg_apply]
  have hS28 : S1.regs 28 = s.regs 28 := by subst hS1; simp [setReg_apply]
  have hS18 : S1.regs 18 = s.regs 18 := by subst hS1; simp [setReg_apply]
  have hSg : S1.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  refine ReachesRet.call (Fv256.Arm64.SfdParse.pu_sum impl p len) (by subst hS1; rfl)
    ⟨by rw [hS30]; decide, by rw [hS30]; decide,
     ⟨by rw [hS28]; exact e6, by rw [hS28, hSacc]; exact e7, by rw [hS28, hSg]; omega⟩,
     ⟨by omega, by omega, by omega, by rw [hSacc, hS1sp]; exact Memory.accessible_mono _ e5 (by omega) (by omega)⟩,
     by subst hS1; simp [setReg_apply, h0], by subst hS1; simp [setReg_apply, h1],
     by subst hS1; simp [setReg_apply, h2], by subst hS1; simp [setReg_apply, h3],
     by rw [hSacc]; exact hch4, hch5, hlen1, hlen2, by omega⟩ ?cont
  case cont =>
    intro s' hpc' ⟨k1, k2, k3, k4, hfr, hcase⟩
    rw [hS1sp] at hfr
    have hchain : ∀ a, (a + 8 ≤ s.sp.toNat - 104 ∨ s.sp.toNat + 48 ≤ a) → S1.mem.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha
      subst hS1; dsimp only
      simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hS1rec : S1.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
        S1.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 := by
      subst hS1; dsimp only
      constructor <;> simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    have hx29 : S1.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      subst hS1; dsimp only
      simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h8]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
    have hx30 : S1.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      subst hS1; dsimp only
      simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      rw [h8]; exact Nat.mod_eq_of_lt (s.regs 30).isLt
    have hxa : S1.mem.readLE (s.sp.toNat + 8) 8 = p.toNat ∧ S1.mem.readLE (s.sp.toNat + 16) 8 = len.toNat ∧
        S1.mem.readLE (s.sp.toNat + 24) 8 = 10 ∧ S1.mem.readLE (s.sp.toNat + 32) 8 = 64 := by
      subst hS1; dsimp only
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, h8]
         try first | exact Nat.mod_eq_of_lt p.isLt | exact Nat.mod_eq_of_lt len.isLt | decide)
    have hout' : ∀ a, (a + 8 ≤ s.sp.toNat - 96 - 56 ∨ s.sp.toNat - 96 - 8 ≤ a) → (a + 8 ≤ s.sp.toNat - 96 + 8 ∨ s.sp.toNat - 96 + 16 ≤ a) →
        s'.mem.readLE a 8 = S1.mem.readLE a 8 := by
      intro a h1 h2
      exact hfr.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
    have hp29 : s'.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
      rw [hout' _ (by te_omega) (by te_omega), hx29]
    have hp30 : s'.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by
      rw [hout' _ (by te_omega) (by te_omega), hx30]
    have hpa : s'.mem.readLE (s.sp.toNat + 8) 8 = p.toNat ∧ s'.mem.readLE (s.sp.toNat + 16) 8 = len.toNat ∧
        s'.mem.readLE (s.sp.toNat + 24) 8 = 10 ∧ s'.mem.readLE (s.sp.toNat + 32) 8 = 64 := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hxa.1
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hxa.2.1
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hxa.2.2.1
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hxa.2.2.2
    have hprec : s'.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
        s'.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 := by
      constructor
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hS1rec.1
      · rw [hout' _ (by te_omega) (by te_omega)]; exact hS1rec.2
    have hfinF : MemFrame s.mem s'.mem [(lo, hi)] := hSf.trans hfr (by
      intro a n h
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      te_omega)
    have hbytes : ∀ k, k < len.toNat → Fv256.C.bytesAt S1.mem p.toNat k = Fv256.C.bytesAt s.mem p.toNat k := by
      intro k hk
      unfold Fv256.C.bytesAt
      exact hSf.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
    have hsp96 : (s.sp - 96#64 + 96#64) = s.sp := by bv_omega
    have hx30S : S1.mem.readLE S1.sp.toNat 8 = (s.regs 30).toNat := by rw [hS1sp]; exact hx30
    have hx29S : S1.mem.readLE (S1.sp.toNat - 8) 8 = (s.regs 29).toNat := by
      rw [hS1sp]; have : s.sp.toNat - 96 - 8 = s.sp.toNat - 104 := by omega
      rw [this]; exact hx29
    rcases hcase with ⟨hA, hv, hz1, hz2⟩ | ⟨hA, hz0, hz1, hz2⟩
    · janus_run [hp29, hp30, hz1, hx30S, hx29S]
      have hS1spb : S1.sp = s.sp - 96#64 := by subst hS1; rfl
      have hspf : S1.sp + 96#64 = s.sp := by rw [hS1spb]; bv_omega
      have hg28 : s'.regs 28 = s.regs 28 := by rw [k3, hS28]
      refine ⟨?_, ?_, ?_, ?_, hprec.1, hprec.2, Or.inl ⟨?_, ?_, ?_, ?_, ?_, hfinF⟩⟩
      · exact hspf
      · simp [setReg_apply]
      · simpa [setReg_apply] using hg28
      · simpa [setReg_apply] using (k4.trans hS18)
      · intro k a b
        have := hA k a b
        rwa [hbytes k b] at this
      · simp only [setReg_apply]; simp only [reduceIte, Nat.reduceEqDiff]
        rw [hv]; exact decSum_congr _ _ 0 _ (fun k _ hk => hbytes k (by omega))
      · simp [setReg_apply]
      · simp [setReg_apply]
      · refine Env.frame0 hMod.1 hEnv ?_ ?_ hfinF (by omega)
        · show lo ≤ (S1.sp + 96#64).toNat ∧ (S1.sp + 96#64).toNat + 8 ≤ hi ∧ (S1.sp + 96#64).toNat % 16 = 0
          rw [hspf]; omega
        · simpa [setReg_apply] using hg28
    · have hS1spb : S1.sp = s.sp - 96#64 := by subst hS1; rfl
      have hne : s'.regs 1 ≠ 0 := by
        intro h; rw [h] at hz1; simp [SfdParse.errItab] at hz1
      janus_run [hp29, hp30, hne, hx30S, hx29S, hpa.1, hpa.2.1, hpa.2.2.1, hpa.2.2.2, hxa.1, hxa.2.1, hxa.2.2.1, hxa.2.2.2] until [te]
      refine reach_name2 ?_
      intro S2 hS2
      have hS2sp : S2.sp = s.sp - 96#64 := by subst hS2; rfl
      have hS2spn : S2.sp.toNat = s.sp.toNat - 96 := by rw [hS2sp]; exact arith_sp _ (by omega) _ rfl
      have hfr2 : MemFrame s'.mem S2.mem [(s.sp.toNat - 16, s.sp.toNat - 8)] := by
        subst hS2; dsimp only; janus_frame
      have hSF : MemFrame s.mem S2.mem [(lo, hi)] := hfinF.trans hfr2 (by
        intro a n h
        simp only [outside_cons, outside_nil, and_true] at h ⊢
        te_omega)
      have hS2g : S2.regs 28 = s.regs 28 := by subst hS2; simpa [setReg_apply] using (k3.trans hS28)
      have hS218 : S2.regs 18 = s.regs 18 := by subst hS2; simpa [setReg_apply] using (k4.trans hS18)
      have hEnv2 : Env R R2 T b L lo hi S2 :=
        Env.frame0 hMod.1 hEnv (by rw [hS2spn]; refine ⟨by omega, by omega, by omega⟩) hS2g hSF (by omega)
      have hEnv3 : Env R R2 T b L (S2.sp.toNat - 4192) (S2.sp.toNat + 72) S2 :=
        Env.shrink hEnv2 (by omega) (by omega) (by omega) (by omega)
      have hS2acc : ∀ a n w, S2.mem.accessible a n w = s.mem.accessible a n w := hSF.accessible
      have hr0 : S2.regs 0 = BitVec.ofNat 64 fnStr := by subst hS2; simp [setReg_apply]
      have hr1 : S2.regs 1 = 9#64 := by subst hS2; simp [setReg_apply]
      have hr2 : S2.regs 2 = p := by subst hS2; simp [setReg_apply]
      have hr3 : S2.regs 3 = len := by subst hS2; simp [setReg_apply]
      have hr30 : S2.regs 30 = 618556#64 := by subst hS2; simp [setReg_apply]
      have hr6 : S2.regs 6 = BitVec.ofNat 64 errItab := by
        subst hS2; simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
        apply BitVec.eq_of_toNat_eq; rw [hz1]; simp only [BitVec.toNat_ofNat]; decide
      have hr7 : S2.regs 7 = BitVec.ofNat 64 synConst := by
        subst hS2; simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
        apply BitVec.eq_of_toNat_eq; rw [hz2]; simp only [BitVec.toNat_ofNat]; decide
      refine ReachesRet.call hte (by subst hS2; rfl) ⟨by rw [hr30]; decide, by rw [hr30]; decide, hr0, hr1, hr2, hr3, hr6, hr7,
        hlen1, by omega, by omega, hMod, hEnv3, hch1, hch2, hch3, by rw [hS2acc]; exact hch4, hch5, by omega, hch7, hch8⟩ ?cont2
      case cont2 =>
        intro s3 hpc3 ⟨c1, c2, c3, c4, ⟨q, t, hr0', hr1', hobj⟩, hfr3, hrecA, hrecB⟩
        have hS2mem : S2.mem = s'.mem.writeLE (s.sp.toNat - 16) 8 0 := by subst hS2; rfl
        have hwin2 : ∀ a n, lo ≤ a → a + n ≤ hi → Outside a n R.rt ∧ Outside a n R2.priv :=
          fun a n h1 h2 => ⟨Outside.of_sub e9 (by te_omega) (by te_omega), Outside.of_sub e10 (by te_omega) (by te_omega)⟩
        have hoo : ∀ a, lo ≤ a → a + 8 ≤ hi → (a + 8 ≤ S2.sp.toNat - 4192 ∨ S2.sp.toNat + 72 ≤ a) →
            s3.mem.readLE a 8 = S2.mem.readLE a 8 := by
          intro a h1 h2 h3
          exact hfr3.readLE _ _ (by
            simp only [outside_append, outside_cons, outside_nil, and_true]
            exact ⟨⟨(hwin2 a 8 h1 h2).1, (hwin2 a 8 h1 h2).2⟩, h3⟩)
        have hq80 : s3.mem.readLE (s.sp.toNat - 16) 8 = 0 := by
          rw [hoo _ (by te_omega) (by te_omega) (by te_omega), hS2mem]
          simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
        have hq80' : s3.mem.readLE (S2.sp.toNat + 80) 8 = 0 := by
          have : S2.sp.toNat + 80 = s.sp.toNat - 16 := by omega
          rw [this]; exact hq80
        have hq29 : s3.mem.readLE (S2.sp.toNat - 8) 8 = (s.regs 29).toNat := by
          rw [hrecA, hS2mem]
          simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
          have : S2.sp.toNat - 8 = s.sp.toNat - 104 := by omega
          rw [this]; exact hp29
        have hq30 : s3.mem.readLE S2.sp.toNat 8 = (s.regs 30).toNat := by
          rw [hrecB, hS2mem]
          simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
          have : S2.sp.toNat = s.sp.toNat - 96 := hS2spn
          rw [this]; exact hp30
        have hprec3 : s3.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧
            s3.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 := by
          constructor
          · rw [hoo _ (by te_omega) (by te_omega) (by te_omega), hS2mem]
            simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
            exact hprec.1
          · rw [hoo _ (by te_omega) (by te_omega) (by te_omega), hS2mem]
            simp (disch := te_omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
            exact hprec.2
        have hq30' : s3.mem.readLE (s.sp.toNat - 96) 8 = (s.regs 30).toNat := by rw [← hS2spn]; exact hq30
        have hq29' : s3.mem.readLE (s.sp.toNat - 104) 8 = (s.regs 29).toNat := by
          have : s.sp.toNat - 104 = S2.sp.toNat - 8 := by omega
          rw [this]; exact hq29
        janus_run [hq29, hq30, hq80, hq80', hq30', hq29']
        have oE := e14 (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
        simp only [Nat.add_sub_cancel_left] at oE
        obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩ := hobj
        have hobj' : TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 p len s s3 q t.toNat := by
          refine ⟨o1, o2, o3, o4, o5, o6, o7, o8, ?_, ?_, ?_, ?_⟩
          · rw [o9]; exact hSF.readLE _ _ (Outside.of_sub oE (by te_omega) (by te_omega))
          · rw [o10]; exact hSF.readLE _ _ (Outside.of_sub oE (by te_omega) (by te_omega))
          · intro k hk
            rw [o11 k hk]
            exact hSF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; te_omega)
          · rw [hS2g] at o12; exact o12
        refine ⟨rfl, ?_, ?_, ?_, hprec3.1, hprec3.2, Or.inr ⟨?_, ?_, ⟨q, t, ?_, ?_, hobj'⟩, ?_⟩⟩
        · simp [setReg_apply]
        · simpa [setReg_apply] using (c3.trans hS2g)
        · simpa [setReg_apply] using (c4.trans hS218)
        · intro h
          apply hA
          intro k a b
          rw [hbytes k b]
          exact h k a b
        · simp [setReg_apply]
        · simpa [setReg_apply] using hr0'
        · simp [setReg_apply]
        · exact hSF.trans hfr3 (by
            intro a n h
            simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
            obtain ⟨⟨h1, h2⟩, h3⟩ := h
            refine ⟨h3, ⟨h1, h2⟩, ?_⟩
            te_omega)

end Fv256.Arm64.SfdPw
