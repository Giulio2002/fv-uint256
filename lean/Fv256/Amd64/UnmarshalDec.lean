import Fv256.Amd64.UnmarshalSpec
import Fv256.Amd64.SbtsFacts
import Fv256.DecCongr

/-!
# `UnmarshalText` decimal branch (amd64): from the state after `string(input)` to `TopPre` of the `SetFromDecimal` call (Extracted-free)

The hypotheses are the facts the engine leaves after the live `runtime.slicebytetostring` contract (buffer `sp - 40`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec

namespace Fv256.Amd64.UnmarshalDec

variable (C : SfdCfg)

structure SbPost (R : RtInv) (st b : Nat) (L : List (Nat × Nat)) (s : State) (pI nI r0 r1 : BitVec 64)
    (M0 m : Janus.Arm64.Memory) : Prop where
  mf : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104),
        ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 24)] ++
      (if (s.regs 4).toNat - 40 = 0 then [] else [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)]))
  soa : (r1.toNat = (strBytes s.mem pI.toNat nI.toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
      (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
      strBytes m r0.toNat r1.toNat = strBytes s.mem pI.toNat nI.toNat) ∧
      StrAt R.rt ((s.regs 4).toNat - 40) st pI.toNat r1.toNat r0.toNat M0
  lf : LiveFrame M0 m L (if (s.regs 4).toNat - 40 = 0 then [] else [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)])
  fr : FreshFrom (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L
  inv : R.inv (b - roundupsize nI.toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 14).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) m)

theorem sfd_inst {C : SfdCfg} {P : Janus.Amd64.Program} {entry : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat}
    {L : List (Nat × Nat)} {lo : Nat} {z pI nI r0 r1 : BitVec 64} {s : State} {M0 m : Janus.Arm64.Memory} {st : Nat}
    (_hP : SbPost R st b L s pI nI r0 r1 M0 m)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary C P entry R R2 T b' L' lo' hi' z pS' nS') :
    SfdSummary C P entry R R2 T (b - roundupsize nI.toNat true)
      (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)])) lo ((s.regs 4).toNat - 40) z r0 nI :=
  hsfd _ _ _ _ _ _ _

theorem m0_frame {R : RtInv} {sb st : Nat} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s : State} {M0 : Janus.Arm64.Memory} {v5 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s)
    (hM0c : M0 = (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 pI.toNat).writeLE
      ((s.regs 4).toNat + 8) 8 z.toNat).writeLE ((s.regs 4).toNat - 104) 8 ra) :
    MemFrame s.mem M0 [(lo, hi)] := by
  have hlo4 := hpre.toS.lo4
  have hhi4 := hpre.toS.hi4
  rw [hM0c]
  refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
    (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
    (by simp) (by omega) (by omega)

theorem dec_call_pre {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {retv v5 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s)
    (hP : SbPost R st b L s pI nI r0 r1 M0 m)
    (hM0c : M0 = (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 pI.toNat).writeLE
      ((s.regs 4).toNat + 8) 8 z.toNat).writeLE ((s.regs 4).toNat - 104) 8 ra)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8)) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = r1) (hr4 : S3.regs 4 = s.regs 4 - 104#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 104) 8 retv) (hretv : retv < 2 ^ 47) :
    TopPre C R R2 T (b - roundupsize nI.toNat true) (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]))
      lo ((s.regs 4).toNat - 40) z r0 nI S3 ∧
    (∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1) ∧
    MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
  obtain ⟨hMF, hSOA, hLF, hFr, hInv⟩ := hP
  have hbne0 : (s.regs 4).toNat - 40 ≠ 0 := by have := hpre.toS.lo4; omega
  rw [if_neg hbne0] at hMF hLF
  obtain ⟨hSO, hSA⟩ := hSOA
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hn : r1.toNat = nI.toNat := by
    rw [hSO.1]; simp
  have hr1' : S3.regs 1 = nI := by rw [hr1]; exact BitVec.eq_of_toNat_eq hn
  have hM0 := m0_frame C hpre hM0c
  have hbne : (s.regs 4).toNat - 40 ≠ 0 := by omega
  have hzr : BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8) = z := by
    have ho : Outside ((s.regs 4).toNat + 8) 8 (R.rt ++ [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104),
        ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 24)] ++ [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega
    rw [hMF.readLE _ _ ho, hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8]; exact Nat.mod_eq_of_lt z.isLt
  rw [hzr] at hr0
  have hadds : ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])) =
      (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]) := by
    rw [Fv256.Amd64.SbtsFacts.adds_eq, hn]
  rw [hadds] at hInv
  rw [hn] at hSO hSA
  -- the frame from the entry memory to the memory at the call
  have hwin2 : MemFrame M0 m (R.rt ++ [(lo, hi)]) := by
    refine MemFrame.mono hMF ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨h1, ?_, ?_⟩, ?_⟩ <;> omega
  have hF1 : MemFrame s.mem m (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hwin2 ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    exact ⟨h.2, h⟩
  have hF : MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
    rw [hS3]
    exact hF1.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hret : S3.mem.readLE ((s.regs 4).toNat - 104) 8 < 2 ^ 47 := by
    rw [hS3, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hretv
  by_cases hz0 : nI.toNat = 0
  · -- empty input: nothing is read, nothing is added to the live set
    refine ⟨?_, fun k hk => absurd hk (by omega), hF⟩
    rw [if_pos hz0] at hInv ⊢
    have hInv' : R.inv (b - roundupsize nI.toNat true) (L ++ []) (S3.regs 14).toNat
        (view R.rt (L ++ []) S3.mem) := by
      rw [hr14, hS3]
      refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 104, (s.regs 4).toNat - 104 + 8)])
        (MemFrame.of_writeLE m _ (r := ((s.regs 4).toNat - 104, (s.regs 4).toNat - 104 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInv
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      left
      rcases hr with rfl
      exact Outside.of_sub e9 (by omega) (by simp only; omega)
    refine toppre_dec C hpre (hi3 := (s.regs 4).toNat - 40) (by omega) (by omega) hr0 hr3 hr1' hr4 hr14 hx15 hdf hret hF
      (L' := L ++ []) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hInv'
    · exact fun r hr => List.mem_append_left _ hr
    · intro r hr
      have h := e18 r (by simpa using hr)
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      omega
    · intro r hr
      exact Mod.lpriv C hp.mod r (by simpa using hr)
    · exact ⟨by have := hSO.2.1; omega, Or.inl hz0⟩
    · exact Or.inl hz0
    · exact Or.inl hz0
    · exact Or.inl hz0
    · exact Or.inl hz0
    · rfl
  · have hpos : 0 < nI.toNat := Nat.pos_of_ne_zero hz0
    have hfr : 32 < nI.toNat → ApartAll r0.toNat nI.toNat L := by
      intro h32
      have := hFr
      rw [hn] at this
      rw [if_pos (by omega), if_neg hz0] at this
      simpa using this _ (List.mem_singleton_self _)
    obtain ⟨hlw, hlp, hlz⟩ := Fv256.Amd64.SbtsFacts.loc (hi3 := (s.regs 4).toNat - 40) hSA hpos (by omega) (by omega)
      (Nat.le_refl _) (by omega) e9 e10 hp.init.2.2.2.2 (Mod.priv C hp.mod) hp.stWin hp.stPriv hp.stZ hp.zwin hp.zR hbne hfr
    rw [if_neg hz0] at hInv ⊢
    have hInv' : R.inv (b - roundupsize nI.toNat true) (L ++ [(r0.toNat, r0.toNat + nI.toNat)]) (S3.regs 14).toNat
        (view R.rt (L ++ [(r0.toNat, r0.toNat + nI.toNat)]) S3.mem) := by
      rw [hr14, hS3]
      refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 104, (s.regs 4).toNat - 104 + 8)])
        (MemFrame.of_writeLE m _ (r := ((s.regs 4).toNat - 104, (s.regs 4).toNat - 104 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInv
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      left
      rcases hr with rfl
      exact Outside.of_sub e9 (by omega) (by simp only; omega)
    have hlw2 : r0.toNat + nI.toNat ≤ lo ∨ (s.regs 4).toNat - 40 ≤ r0.toNat := by
      have h := hlw
      simp only [outside_cons, outside_nil, and_true] at h
      exact h
    have hbytes : ∀ k, k < nI.toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE (pI.toNat + k) 1 := by
      intro k hk
      have hq := congrArg (fun l => l.getD k 0) hSO.2.2.2
      rw [strBytes_getD _ _ _ _ (by omega), strBytes_getD _ _ _ _ (by omega)] at hq
      rw [hS3]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one]
      exact hq
    refine ⟨?_, hbytes, hF⟩
    refine toppre_dec C hpre (hi3 := (s.regs 4).toNat - 40) (by omega) (by omega) hr0 hr3 hr1' hr4 hr14 hx15 hdf hret hF
      (L' := L ++ [(r0.toNat, r0.toNat + nI.toNat)]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hInv'
    · exact fun r hr => List.mem_append_left _ hr
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · have := e18 r h
        simp only [outside_cons, outside_nil, and_true] at this ⊢
        omega
      · simp only [List.mem_singleton] at h
        subst h
        rw [Nat.add_sub_cancel_left]; exact hlw
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact Mod.lpriv C hp.mod r h
      · simp only [List.mem_singleton] at h
        subst h
        rw [Nat.add_sub_cancel_left]; exact hlp
    · refine ⟨by have := hSO.2.1; omega, Or.inr ?_⟩
      rw [hF.accessible]; exact hSO.2.2.1 hpos
    · right
      simp only [outside_cons, outside_nil, and_true] at hlw
      exact hlw
    · exact Or.inr hlz
    · exact Or.inr (Or.inr ⟨(r0.toNat, r0.toNat + nI.toNat), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
    · exact Or.inr hlp
    · rfl

/-- the saved `RBP` and the return address are unchanged at the end: they are outside every frame -/
theorem ret_reads {R : RtInv} {lo hi sp v5 vp vz ra ra' : Nat} {s0 M0 m S3m S' : Janus.Arm64.Memory}
    (hlo : lo + 4904 ≤ sp) (hhi : sp + 24 ≤ hi) (hrt : Outside lo (hi - lo) R.rt)
    (hM0 : M0 = (((s0.writeLE (sp - 8) 8 v5).writeLE (sp + 16) 8 vp).writeLE (sp + 8) 8 vz).writeLE (sp - 104) 8 ra)
    (hMF : MemFrame M0 m (R.rt ++ [(sp - 104 - 4096, sp - 104), (sp - 104 + 8, sp - 104 + 8 + 24)] ++ [(sp - 40, sp - 40 + 32)]))
    (hS3 : S3m = m.writeLE (sp - 104) 8 ra')
    {W : List (Nat × Nat)} (cMF : MemFrame S3m S' W) (hW : ∀ a, a = sp ∨ a = sp - 8 → Outside a 8 W) :
    S'.readLE sp 8 = s0.readLE sp 8 ∧ S'.readLE (sp - 8) 8 = v5 % 2 ^ 64 := by
  have o1 : ∀ a, a = sp ∨ a = sp - 8 → Outside a 8 W := hW
  have o2 : ∀ a, a = sp ∨ a = sp - 8 →
      Outside a 8 (R.rt ++ [(sp - 104 - 4096, sp - 104), (sp - 104 + 8, sp - 104 + 8 + 24)] ++ [(sp - 40, sp - 40 + 32)]) := by
    intro a ha
    simp only [outside_append, outside_cons, outside_nil, and_true]
    refine ⟨⟨Outside.of_sub hrt (by omega) (by omega), ?_, ?_⟩, ?_⟩ <;> omega
  have step : ∀ a, a = sp ∨ a = sp - 8 → S'.readLE a 8 = M0.readLE a 8 := by
    intro a ha
    rw [cMF.readLE a 8 (o1 a ha), hS3]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hMF.readLE a 8 (o2 a ha)
  constructor
  · rw [step sp (Or.inl rfl), hM0]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · rw [step (sp - 8) (Or.inr rfl), hM0]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]

/-- the results of the decimal branch about the final state `s'` of the `SetFromDecimal` call -/
theorem dec_post {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 s' : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {retv v5 ra : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s)
    (hP : SbPost R st b L s pI nI r0 r1 M0 m)
    (hM0c : M0 = (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 pI.toNat).writeLE
      ((s.regs 4).toNat + 8) 8 z.toNat).writeLE ((s.regs 4).toNat - 104) 8 ra)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 104) 8 retv)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8)) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = r1)
    (hr4 : S3.regs 4 = s.regs 4 - 104#64) (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hretv : retv < 2 ^ 47)
    (hq : TopPost C R R2 T (b - roundupsize nI.toNat true)
      (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)])) lo ((s.regs 4).toNat - 40) z r0 nI S3 s') :
    ((∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
        s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
      (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
        (s'.regs 0).toNat = s.mem.readLE C.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.ioEOF + 8) 8 ∧
        Janus.Spec.val256 s'.mem z.toNat = 0) ∧
      (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
        (s'.regs 0).toNat = s.mem.readLE C.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.errBig + 8) 8 ∧
        Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
      (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
        s'.regs 0 = BitVec.ofNat 64 C.numErrItab)) ∧
    MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
    (s'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
      s'.mem.readLE ((s.regs 4).toNat - 8) 8 = v5 % 2 ^ 64) := by
  obtain ⟨hKept, hcases⟩ := hq
  have hM0 := m0_frame C hpre hM0c
  obtain ⟨-, hbytes, hF⟩ := dec_call_pre C hpre hP hM0c hr0 hr3 hr1 hr4 hr14 hx15 hdf hS3 hretv
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hdp : decParse (bytesAt S3.mem r0.toNat) nI.toNat = decParse (bytesAt s.mem pI.toNat) nI.toNat :=
    Fv256.I.decParse_congr _ _ _ (fun k hk => hbytes k hk)
  have hio : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have hzsame : Janus.Spec.val256 S3.mem z.toNat = Janus.Spec.val256 s.mem z.toNat := by
    have hzw := hp.zwin
    rcases hp.zR with h | h
    · exact hF.readLE z.toNat 32 (by
        rw [outside_append]
        refine ⟨h, ?_⟩
        simp only [outside_cons, outside_nil, and_true]; omega)
    · obtain ⟨-, -, hLF, -, -⟩ := hP
      have hne : (s.regs 4).toNat - 40 ≠ 0 := by omega
      rw [if_neg hne] at hLF
      unfold Janus.Spec.val256
      rw [hS3]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hLF.readLE z.toNat 32 h (by simp only [outside_cons, outside_nil, and_true]; omega)]
      exact hM0.readLE z.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hzw := hp.zwin
  have hMFof : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104),
      ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 24)] ++ [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)]) := by
    obtain ⟨hMF, -, -, -, -⟩ := hP
    have hne : (s.regs 4).toNat - 40 ≠ 0 := by omega
    rw [if_neg hne] at hMF
    exact hMF
  have fin : MemFrame S3.mem s'.mem (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (z.toNat, z.toNat + 32)]) →
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)]) ∧
      (s'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
        s'.mem.readLE ((s.regs 4).toNat - 8) 8 = v5 % 2 ^ 64) := by
    intro cMF
    refine ⟨hF.trans cMF ?_, ?_⟩
    · intro a n h
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
      exact ⟨⟨h1, h3⟩, ⟨h1, h2⟩, by omega, h4⟩
    · refine ret_reads (R := R) hlo4 hhi4 e9 hM0c hMFof hS3 cMF ?_
      intro a ha
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, ?_, ?_⟩ <;> omega
  rcases hcases with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c3, cTe, cMF⟩
  · refine ⟨⟨fun v' hv' => ?_, fun h => ?_, fun h => ?_, fun _ _ h => ?_⟩, fin (cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2))⟩
    · rw [← hdp] at hv'
      rw [hv] at hv'; cases hv'
      exact ⟨c0, c3, cval⟩
    all_goals (rw [← hdp] at h; rw [hv] at h; cases h)
  · refine ⟨⟨fun v' h => ?_, fun _ => ?_, fun h => ?_, fun _ _ h => ?_⟩, fin (cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2))⟩
    · rw [← hdp] at h; rw [hv] at h; cases h
    · have e1 := hp.eofW
      have e2 := hp.eofR
      simp only [outside_cons, outside_nil, and_true] at e1
      refine ⟨?_, ?_, cval⟩
      · rw [c0]; exact hio _ _ (Outside.of_sub e2 (Nat.le_refl _) (by omega)) (by
          simp only [outside_cons, outside_nil, and_true]; omega)
      · rw [c3]; exact hio _ _ (Outside.of_sub e2 (by omega) (by omega)) (by
          simp only [outside_cons, outside_nil, and_true]; omega)
    all_goals (rw [← hdp] at h; rw [hv] at h; cases h)
  · refine ⟨⟨fun v' h => ?_, fun h => ?_, fun _ => ?_, fun _ _ h => ?_⟩, fin (cMF.mono (fun a n h => by rw [outside_append] at h; exact h.2))⟩
    · rw [← hdp] at h; rw [hv] at h; cases h
    · rw [← hdp] at h; rw [hv] at h; cases h
    · have e1 := hp.bigW
      have e2 := hp.bigR
      simp only [outside_cons, outside_nil, and_true] at e1
      refine ⟨?_, ?_, by rw [cval]; exact hzsame⟩
      · rw [c0]; exact hio _ _ (Outside.of_sub e2 (Nat.le_refl _) (by omega)) (by
          simp only [outside_cons, outside_nil, and_true]; omega)
      · rw [c3]; exact hio _ _ (Outside.of_sub e2 (by omega) (by omega)) (by
          simp only [outside_cons, outside_nil, and_true]; omega)
    · rw [← hdp] at h; rw [hv] at h; cases h
  · refine ⟨⟨fun v' h => ?_, fun h => ?_, fun h => ?_, fun _ _ _ => c0⟩, fin cMF⟩
    all_goals (rw [← hdp] at h; rw [hv] at h; cases h)

end Fv256.Amd64.UnmarshalDec
