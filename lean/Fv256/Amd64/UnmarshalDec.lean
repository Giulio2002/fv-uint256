import Fv256.Amd64.UnmarshalSpec
import Fv256.Amd64.SbtsFacts

/-!
# `UnmarshalText` decimal branch (amd64): from the state after `string(input)` to `TopPre` of the `SetFromDecimal` call (Extracted-free)

The hypotheses are the facts the engine leaves after the live `runtime.slicebytetostring` contract (buffer `sp - 40`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec

namespace Fv256.Amd64.UnmarshalDec

variable (C : SfdCfg)

theorem dec_call_pre {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pI nI : BitVec 64} {s S3 : State} {M0 m : Janus.Arm64.Memory} {r0 r1 : BitVec 64} {retv : Nat}
    (hpre : PreU C sb st R R2 T b L lo hi z pI nI s)
    (hM0 : MemFrame s.mem M0 [(lo, hi)])
    (hMF : MemFrame M0 m (R.rt ++ [((s.regs 4).toNat - 104 - 4096, (s.regs 4).toNat - 104),
        ((s.regs 4).toNat - 104 + 8, (s.regs 4).toNat - 104 + 8 + 24)] ++ [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)]))
    (hSO : r1.toNat = (strBytes s.mem pI.toNat nI.toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
      (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
      strBytes m r0.toNat r1.toNat = strBytes s.mem pI.toNat nI.toNat)
    (hSA : StrAt R.rt ((s.regs 4).toNat - 40) st pI.toNat r1.toNat r0.toNat M0)
    (hLF : LiveFrame M0 m L [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)])
    (hFr : FreshFrom (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L)
    (hInv : R.inv (b - roundupsize nI.toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 14).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ ((s.regs 4).toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) m))
    (hr0 : S3.regs 0 = z) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = nI) (hr4 : S3.regs 4 = s.regs 4 - 104#64)
    (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 104) 8 retv) (hretv : retv < 2 ^ 47) :
    TopPre C R R2 T (b - roundupsize nI.toNat true) (L ++ (if nI.toNat = 0 then [] else [(r0.toNat, r0.toNat + nI.toNat)]))
      lo ((s.regs 4).toNat - 40) z r0 nI S3 := by
  have hp := hpre.toS
  have hlo4 := hp.lo4
  have hhi4 := hp.hi4
  have hEnv := hp.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hn : r1.toNat = nI.toNat := by
    rw [hSO.1]; simp
  have hbne : (s.regs 4).toNat - 40 ≠ 0 := by omega
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
  · -- empty input: awaiting the `nS = 0 ∨ …` guard of `accessible` in `TopPre`
    sorry
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
    refine toppre_dec C hpre (hi3 := (s.regs 4).toNat - 40) (by omega) (by omega) hr0 hr3 hr1 hr4 hr14 hx15 hdf hret hF
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
    · refine ⟨by have := hSO.2.1; omega, ?_⟩
      rw [hF.accessible]; exact hSO.2.2.1 hpos
    · right
      simp only [outside_cons, outside_nil, and_true] at hlw
      exact hlw
    · exact Or.inr hlz
    · exact Or.inr ⟨(r0.toNat, r0.toNat + nI.toNat), List.mem_append_right _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩
    · exact hlp
    · rfl

end Fv256.Amd64.UnmarshalDec
