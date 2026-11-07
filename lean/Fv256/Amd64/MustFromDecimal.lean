import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.DecCongr

/-!
# `uint256.MustFromDecimal(decimal string) (*Int, error)` (amd64)   (conditional on the `SetFromDecimal` summary `hsfd`)

`var z Int; if err := z.SetFromDecimal(decimal); err != nil { panic(err) }; return &z`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Janus.Contracts.PanicAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.MustFromDecimal

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg :=
  (Extracted.dataAddr.«io.EOF»,
    Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»,
    Extracted.dataAddr.«github.com/holiman/uint256.multipliers»,
    Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»,
    Extracted.dataAddr.«go:itab.*strconv.NumError,error»,
    Extracted.dataAddr.«go:itab.internal/strconv.Error,error»,
    Extracted.dataAddr.«.rodata#9967e7a3»,
    Extracted.dataAddr.«strconv.ErrSyntax»,
    Extracted.dataAddr.«runtime.writeBarrier»,
    Extracted.dataAddr.«.rodata#3d2a826c»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

open Fv256.C in
/-- precondition of `MustFromDecimal(s)` (string pointer in `RAX`, length in `RBX`): `FromDecimalSpec.PreC` plus the rodata and `PanicInit` -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Amd64.FromDecimalSpec.PreC0 cfg R R2 T b L lo hi Extracted.dataAddr.«type:uint256.Int#33f34945» pS nS s ∧
  Extracted.program.DataLoaded s.mem ∧ Fv256.Amd64.FromDecimalSpec.PanicInit cfg R R2 lo hi s.mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Fv256.C in
theorem correctness_cond (P : Janus.Spec.PanicRuntime) (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]))
      (fun s v _ =>
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
        (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
          InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hpreC0, hdl, hPI⟩ := hpre
  refine GoReturns.of_reaches ?_
  have hpreC := Fv256.Amd64.FromDecimalSpec.PreC.of0 cfg (Fv256.Amd64.FromDecimalSpec.PreC0.retOK cfg hpreC0 h_x15 h_df (by rw [h_ret]; exact hret.user)) hpreC0
  have hpreC' := hpreC
  obtain ⟨hRet, h0, h3, hMod, hEnv, hlo, hhi, hok, hbud, -⟩ := hpreC'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18⟩ := hEnv'
  janus64_data hdl [hr5]
  janus_eval_nat h_pt : Extracted.dataAddr.«type:uint256.Int#33f34945»
  rw [h_pt] at hok
  janus64_run until [Extracted.entry + 0x34] calls [hnew.pos]
  rename_i zv _ _ _ _ mN _ _ hLF hMF hApL hInR hLe hAcc h8 h16 hZB hT hAp3 hInvM hApWin
  janus64_run until [sfdEntry]
  have hM0 : MemFrame s.mem ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 nS.toNat).writeLE
      ((s.regs 4).toNat + 8) 8 pS.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933061) [(lo, hi)] := by
    refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)
  have hF1 : MemFrame s.mem mN (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hMF ?_
    intro a n h
    exact Fv256.Amd64.FromDecimalSpec.outside_sub_stack R.rt lo hi _ a n hlo hhi h
  have hF : MemFrame s.mem ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933081)
      (R.rt ++ [(lo, hi)]) :=
    (hF1.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hInv' : R.inv (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) (s.regs 14).toNat
      (view R.rt (L ++ [(zv.toNat, zv.toNat + 32)])
        ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933081)) := by
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)])
      ((MemFrame.of_writeLE mN _ (r := ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)).writeLE _
        (r := ((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInvM
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    left
    rcases hr with rfl | rfl <;> exact Outside.of_sub hr9 (by omega) (by simp only; omega)
  obtain ⟨hS_ret, hS_rbp, hS_z⟩ := Fv256.Amd64.FromDecimalSpec.s3_reads (v5 := (s.regs 5).toNat) (vn := nS.toNat)
    (vp := pS.toNat) (zN := zv.toNat) (ra := 4933061) (rc := 4933081) hlo hhi hr9 hMF
  have hbytes : ∀ k, k < nS.toNat → bytesAt ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933081) pS.toNat k
      = bytesAt s.mem pS.toNat k := by
    intro k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPS, hPR, -⟩ := hpreC
    unfold bytesAt
    have hk' : pS.toNat + k < pS.toNat + nS.toNat := by omega
    refine Fv256.Amd64.FromDecimalSpec.str_read hlo hhi hM0 hMF hLF (by omega) ?_
    rcases hPR with h | h
    · exact Or.inl (Outside.of_sub h (by omega) (by omega))
    · exact Or.inr (InRanges.sub h (by omega) (by omega))
  refine Reaches.call (Summary.withExit (hsfd (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) lo ((s.regs 4).toNat - 16) zv pS nS) hret) ?_ ?_ ?_
  · first | rfl | decide
  · refine Fv256.Amd64.FromDecimalSpec.toppre_of_call cfg hpreC (hi3 := (s.regs 4).toNat - 16) (by omega) (Nat.le_refl _) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply])
      (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp) (by simpa using h_df) ?_ hF hInR hApL hAcc (by omega) hInv'
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    decide
  · intro s' hr hq
    obtain ⟨hKept, hcases⟩ := hq
    dsimp only at hcases
    rw [Fv256.I.decParse_congr _ (bytesAt s.mem pS.toNat) nS.toNat hbytes] at hcases
    obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKept
    rcases hcases with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hv, c0, c3, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c3, cTe, cMF⟩
    · have hoS : ∀ a n, a + n ≤ lo ∨ (s.regs 4).toNat - 16 ≤ a → a + n ≤ zv.toNat ∨ zv.toNat + 32 ≤ a →
          Outside a n [(lo, (s.regs 4).toNat - 16), (zv.toNat, zv.toNat + 32)] := by
        intro a n h1 h2
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨h1, h2⟩
      have hs_ret : s'.mem.readLE (s.regs 4).toNat 8 = ret := by
        rw [cMF.readLE _ _ (hoS _ _ (Or.inr (by omega)) (by unfold Apart at hApWin; omega)), hS_ret]
        exact h_ret
      have hs_rbp : s'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [cMF.readLE _ _ (hoS _ _ (Or.inr (by omega)) (by unfold Apart at hApWin; omega)), hS_rbp]
        exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this)
      have hs_z : s'.mem.readLE ((s.regs 4).toNat - 16) 8 = zv.toNat := by
        rw [cMF.readLE _ _ (hoS _ _ (Or.inr (by omega)) (by unfold Apart at hApWin; omega)), hS_z]
        exact Nat.mod_eq_of_lt (by have := zv.isLt; simpa using this)
      janus64_run [hs_ret, hs_rbp, hs_z]
      have hFr : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]) := by
        refine hF.trans cMF ?_
        intro a n h
        simp only [outside_append] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine ⟨by rw [outside_append]; exact ⟨h1, h3⟩, ?_⟩
        have h4 := InRanges.apart hInR h1
        unfold Apart at h4
        simp only [outside_cons, outside_nil, and_true] at h3 ⊢
        omega
      refine ⟨⟨v, hv⟩, fun v' hv' => ⟨zv.toNat, rfl, hInR, ?_⟩, hFr⟩
      have : v = v' := by
        rw [hv] at hv'; cases hv'; rfl
      rw [← this]; exact cval
    · -- io.EOF
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE2, hE3, -, hB2, hB3, hInit, -, -, -, -, -, -, -, -⟩ := hpreC
      obtain ⟨hPI1, hPI2, hPI3, hPI4, hPI5⟩ := hPI
      have hio : ∀ a, a = cfg.ioEOF ∨ a = cfg.ioEOF + 8 → ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933081).readLE a 8
          = s.mem.readLE a 8 := by
        intro a ha
        refine hF.readLE a 8 ?_
        rw [outside_append]
        refine ⟨?_, ?_⟩
        · rcases ha with rfl | rfl
          · exact Outside.of_sub hE3 (by omega) (by omega)
          · exact Outside.of_sub hE3 (by omega) (by omega)
        · simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
          rcases ha with rfl | rfl <;> omega
      have hnz : s'.regs 0 ≠ 0 := by
        intro h0'
        rw [h0', hio _ (Or.inl rfl)] at c0
        exact hInit.1 (by simpa using c0.symm)
      have hnz' : ¬ (s'.regs 0).toNat = 0 := fun h => hnz (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨hI0, hI1, hI2, hI3⟩ := hPI1 (s.mem.readLE cfg.ioEOF 8) (Or.inl rfl)
      have hP' : s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8 := by
        rw [c0, hio _ (Or.inl rfl)]
        rw [cMF.readLE _ _ (by
          simp only [outside_cons, outside_nil, and_true]
          have := InRanges.apart hInR hI2
          unfold Apart at this
          simp only [outside_cons, outside_nil, and_true] at hI3
          exact ⟨by omega, by omega⟩)]
        refine hF.readLE _ _ ?_
        rw [outside_append]
        exact ⟨hI2, hI3⟩
      have hAc : s'.mem.accessible (((s'.regs 0).toNat + 8) % 18446744073709551616) 8 false = true := by
        rw [c0, hio _ (Or.inl rfl), Nat.mod_eq_of_lt (by omega), cMF.accessible, hF.accessible]
        exact hI1
      janus64_run [hnz', hP', hAc]
      refine ⟨⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩, ?_, Or.inl ⟨hv, rfl⟩⟩
      simp only [goClass, if_true, setRegF_apply]
      have hw : (s'.regs 0).toNat + 8 < 18446744073709551616 := by rw [c0, hio _ (Or.inl rfl)]; omega
      simp only [Janus.Eface.mk.injEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at *
      refine ⟨?_, ?_⟩
      · rw [hP']; exact (Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)).symm
      · rw [if_neg (by decide), if_neg (by decide), c3, hio _ (Or.inr rfl)]
    · -- ErrBig256Range
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, hE3, hInit, -, -, -, -, -, -, -, -⟩ := hpreC
      obtain ⟨hPI1, hPI2, hPI3, hPI4, hPI5⟩ := hPI
      have hio : ∀ a, a = cfg.errBig ∨ a = cfg.errBig + 8 → ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4933081).readLE a 8
          = s.mem.readLE a 8 := by
        intro a ha
        refine hF.readLE a 8 ?_
        rw [outside_append]
        refine ⟨?_, ?_⟩
        · rcases ha with rfl | rfl
          · exact Outside.of_sub hE3 (by omega) (by omega)
          · exact Outside.of_sub hE3 (by omega) (by omega)
        · simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
          rcases ha with rfl | rfl <;> omega
      have hnz : s'.regs 0 ≠ 0 := by
        intro h0'
        rw [h0', hio _ (Or.inl rfl)] at c0
        exact hInit.2.2.1 (by simpa using c0.symm)
      have hnz' : ¬ (s'.regs 0).toNat = 0 := fun h => hnz (BitVec.eq_of_toNat_eq (by simpa using h))
      obtain ⟨hI0, hI1, hI2, hI3⟩ := hPI1 (s.mem.readLE cfg.errBig 8) (Or.inr rfl)
      have hP' : s'.mem.readLE ((s'.regs 0).toNat + 8) 8 = s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8 := by
        rw [c0, hio _ (Or.inl rfl)]
        rw [cMF.readLE _ _ (by
          simp only [outside_cons, outside_nil, and_true]
          have := InRanges.apart hInR hI2
          unfold Apart at this
          simp only [outside_cons, outside_nil, and_true] at hI3
          exact ⟨by omega, by omega⟩)]
        refine hF.readLE _ _ ?_
        rw [outside_append]
        exact ⟨hI2, hI3⟩
      have hAc : s'.mem.accessible (((s'.regs 0).toNat + 8) % 18446744073709551616) 8 false = true := by
        rw [c0, hio _ (Or.inl rfl), Nat.mod_eq_of_lt (by omega), cMF.accessible, hF.accessible]
        exact hI1
      janus64_run [hnz', hP', hAc]
      refine ⟨⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩, ?_, Or.inr (Or.inl ⟨hv, rfl⟩)⟩
      simp only [goClass, if_true, setRegF_apply]
      have hw : (s'.regs 0).toNat + 8 < 18446744073709551616 := by rw [c0, hio _ (Or.inl rfl)]; omega
      simp only [Janus.Eface.mk.injEq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw] at *
      refine ⟨?_, ?_⟩
      · rw [hP']; exact (Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)).symm
      · rw [if_neg (by decide), if_neg (by decide), c3, hio _ (Or.inr rfl)]

    · -- syntax error
      obtain ⟨hPI1, hPI2, hPI3, hPI4, hPI5⟩ := hPI
      have hnz' : ¬ (s'.regs 0).toNat = 0 := by
        rw [c0]; decide
      have hnum : ¬ cfg.numErrItab = 0 := by decide
      have hApN : Apart cfg.numErrItab 16 zv.toNat 32 := InRanges.apart hInR hPI2
      have hP2 : s'.mem.readLE (cfg.numErrItab + 8) 8 = s.mem.readLE (cfg.numErrItab + 8) 8 := by
        rw [cMF.readLE _ _ (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          unfold Apart at hApN
          refine ⟨⟨Outside.of_sub hPI2 (by omega) (by omega), Outside.of_sub hPI4 (by omega) (by omega)⟩, ?_, ?_⟩
          · simp only [outside_cons, outside_nil, and_true] at hPI3; omega
          · omega)]
        refine hF.readLE _ _ ?_
        rw [outside_append]
        simp only [outside_cons, outside_nil, and_true] at hPI3 ⊢
        exact ⟨Outside.of_sub hPI2 (by omega) (by omega), by omega⟩
      have hAc : s'.mem.accessible (((s'.regs 0).toNat + 8) % 18446744073709551616) 8 false = true := by
        rw [c0]
        simp only [BitVec.toNat_ofNat]
        rw [cMF.accessible, hF.accessible]
        have : (cfg.numErrItab % 18446744073709551616 + 8) % 18446744073709551616 = cfg.numErrItab + 8 := by
          decide
        rw [this]
        exact Janus.Arm64.Memory.accessible_sub s.mem hPI5 (Or.inl rfl) (by omega) (by omega)
      janus64_run [hnz', hnum, hP2, hAc]
      refine ⟨⟨dataReadD Extracted.program (cfg.numErrItab + 8) 8, (s'.regs 3).toNat⟩, ?_,
        Or.inr (Or.inr ⟨lo', len', (s'.regs 3).toNat, hv, ?_, rfl⟩)⟩
      · simp only [goClass, if_true, setRegF_apply]
        simp only [Janus.Eface.mk.injEq, BitVec.toNat_ofNat]
        refine ⟨?_, ?_⟩
        · have hd : dataReadD Extracted.program (cfg.numErrItab + 8) 8 = s.mem.readLE (cfg.numErrItab + 8) 8 :=
            (h_rodata _ _ (by decide)).symm
          rw [hd]; exact (Nat.mod_eq_of_lt (Janus.Arm64.Memory.readLE_lt _ _ 8)).symm
        · rw [if_neg (by decide), if_neg (by decide)]
      · rw [c3]; exact cTe.2.1

end Fv256.Amd64.MustFromDecimal
