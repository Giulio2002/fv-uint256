import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.FromDecimalSpec
import Fv256.DecCongr

/-!
# `uint256.FromDecimal(decimal string) (*Int, error)` (arm64)   (conditional on the `SetFromDecimal` summary `hsfd`)

`var z Int; if err := z.SetFromDecimal(decimal); err != nil { return nil, err }; return &z, nil`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.FromDecimal

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg where
  ioEOF := Extracted.dataAddr.«io.EOF»
  errBig := Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»
  mulTab := Extracted.dataAddr.«github.com/holiman/uint256.multipliers»
  numErrType := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
  numErrItab := Extracted.dataAddr.«go:itab.*strconv.NumError,error»
  errItab := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
  synConst := Extracted.dataAddr.«.rodata#9967e7a3»
  strconvErrSyntax := Extracted.dataAddr.«strconv.ErrSyntax»
  wbFlag := Extracted.dataAddr.«runtime.writeBarrier»
  fnStr := Extracted.dataAddr.«.rodata#7233b75a»
  maxStr := Extracted.dataAddr.«.rodata#575028b4»
  mallocgc := Extracted.program.contractAddr "runtime.mallocgc"
  memmove := Extracted.program.contractAddr "runtime.memmove"
  newobject := Extracted.program.contractAddr "runtime.newobject"
  wb1 := Extracted.program.contractAddr "runtime.gcWriteBarrier1"
  wb2 := Extracted.program.contractAddr "runtime.gcWriteBarrier2"

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

open Fv256.C in
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Arm64.FromDecimalSpec.PreC cfg R R2 T b L lo hi Extracted.dataAddr.«type:uint256.Int#33f34945» pS nS s ∧
  Extracted.program.DataLoaded s.mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Fv256.C in
theorem correctness (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun s s' =>
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof →
          s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.ioEOF + 8) 8) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range →
          s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.errBig + 8) 8) ∧
        (∀ lo' len', decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' →
          s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 cfg.numErrItab) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])) := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hpreC, hdl⟩ := hpre
  have hpreC' := hpreC
  obtain ⟨h30a, h30b, h0, h1, hMod, hEnv, hlo, hhi, hok, hbud, -⟩ := hpreC'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18⟩ := hEnv'
  janus_data hdl [hr5]
  janus_eval_nat h_pt : Extracted.dataAddr.«type:uint256.Int#33f34945»
  rw [h_pt] at hok
  janus_run until [Extracted.entry + 0x2c] calls [hnew.pos]
  rename_i zv _ _ _ mN _ _ hLF hMF hApL hInR hLe hAcc h8 h16 hZB hT hAp3 hInvM hApWin
  have hM0 : MemFrame s.mem ((((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
      (s.sp.toNat + 16) 8 nS.toNat).writeLE (s.sp.toNat + 8) 8 pS.toNat) [(lo, hi)] := by
    refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)
  have hF1 : MemFrame s.mem mN (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hMF ?_
    intro a n h
    exact Fv256.Arm64.FromDecimalSpec.outside_sub_stack R.rt lo hi _ a n hlo hhi h
  have hF : MemFrame s.mem (mN.writeLE (s.sp.toNat - 16) 8 zv.toNat) (R.rt ++ [(lo, hi)]) :=
    hF1.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  obtain ⟨hS_ra, hS_fp, hS_z⟩ := Fv256.Arm64.FromDecimalSpec.s3_reads (v29 := (s.regs 29).toNat) (vn := nS.toNat)
    (vp := pS.toNat) (zN := zv.toNat) (ra := ret) hlo hhi hr9 hMF
  have hbytes : ∀ k, k < nS.toNat → bytesAt (mN.writeLE (s.sp.toNat - 16) 8 zv.toNat) pS.toNat k = bytesAt s.mem pS.toNat k := by
    intro k hk
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPS, hPR, -⟩ := hpreC
    unfold bytesAt
    have hk' : pS.toNat + k < pS.toNat + nS.toNat := by omega
    refine Fv256.Arm64.FromDecimalSpec.str_read hlo hhi hM0 hMF hLF (by omega) ?_
    rcases hPR with h | h
    · exact Or.inl (Outside.of_sub h (by omega) (by omega))
    · exact Or.inr (InRanges.sub h (by omega) (by omega))
  have hInv' : R.inv (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) (s.regs 28).toNat
      (view R.rt (L ++ [(zv.toNat, zv.toNat + 32)]) (mN.writeLE (s.sp.toNat - 16) 8 zv.toNat)) := by
    refine RtInv.inv_frame' (ws := [(s.sp.toNat - 16, s.sp.toNat - 16 + 8)])
      (MemFrame.of_writeLE mN _ (r := (s.sp.toNat - 16, s.sp.toNat - 16 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInvM
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    left
    rcases hr with rfl
    exact Outside.of_sub hr9 (by omega) (by simp only; omega)
  janus_run until [sfdEntry]
  refine Reaches.call (Summary.withExit (hsfd (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) lo (s.sp.toNat - 16) zv pS nS) hret) ?_ ?_ ?_
  · first | rfl | decide
  · refine Fv256.Arm64.FromDecimalSpec.toppre_of_call cfg hpreC (hi3 := s.sp.toNat - 16) (by omega) (Nat.le_refl _)
      (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
      hF hInR hApL hAcc (by omega) hInv'
  · intro s' hr hq
    obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hq
    dsimp only at hcases k1 k2 k3 k4 k5 k6
    rw [Fv256.I.decParse_congr _ (bytesAt s.mem pS.toNat) nS.toNat hbytes] at hcases
    have hretlt : ret % 2 ^ 64 = ret := Nat.mod_eq_of_lt (by have := hret.user; omega)
    rcases hcases with ⟨v, hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨hv, c0, c1, cval, cEnv, cMF⟩ | ⟨lo', len', hv, q, t, c0, c1, cTe, cMF⟩
    · have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
        have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [hsp48] at k5 k6
      have hs_fp : s'.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
        rw [show s.sp.toNat - 56 = s.sp.toNat - 48 - 8 by omega, k5, show s.sp.toNat - 48 - 8 = s.sp.toNat - 56 by omega, hS_fp]
        exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
      have hs_ra : s'.mem.readLE (s.sp.toNat - 48) 8 = ret := by
        rw [k6, hS_ra, hretlt]
      have hoS : ∀ a n, a + n ≤ lo ∨ s.sp.toNat - 16 ≤ a → a + n ≤ zv.toNat ∨ zv.toNat + 32 ≤ a →
          Outside a n [(lo, s.sp.toNat - 16), (zv.toNat, zv.toNat + 32)] := by
        intro a n h1 h2
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨h1, h2⟩
      have hs_z : s'.mem.readLE (s.sp.toNat - 16) 8 = zv.toNat := by
        rw [cMF.readLE _ _ (hoS _ _ (Or.inr (by omega)) (by unfold Apart at hApWin; omega)), hS_z]
        exact Nat.mod_eq_of_lt (by have := zv.isLt; simpa using this)
      janus_run [hs_ra, hs_fp, hs_z]
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
      refine ⟨fun v' hv' => ⟨zv.toNat, rfl, hInR, ?_⟩, ?_, ?_, ?_, hFr⟩
      · have : v = v' := by
          rw [hv] at hv'; cases hv'; rfl
        rw [← this]; simpa [val256, Util.readLE_32] using cval
      · intro h; rw [hv] at h; cases h
      · intro h; rw [hv] at h; cases h
      · intro _ _ h; rw [hv] at h; cases h
    · -- io.EOF
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, hE3, -, -, -, hInit, -, -, -, -, -, -, -, -, -⟩ := hpreC
      have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
        have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [hsp48] at k5 k6
      have hs_fp : s'.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
        rw [show s.sp.toNat - 56 = s.sp.toNat - 48 - 8 by omega, k5, show s.sp.toNat - 48 - 8 = s.sp.toNat - 56 by omega, hS_fp]
        exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
      have hs_ra : s'.mem.readLE (s.sp.toNat - 48) 8 = ret := by
        rw [k6, hS_ra, hretlt]
      have hoS : ∀ a n, a + n ≤ lo ∨ s.sp.toNat - 16 ≤ a → a + n ≤ zv.toNat ∨ zv.toNat + 32 ≤ a →
          Outside a n [(lo, s.sp.toNat - 16), (zv.toNat, zv.toNat + 32)] := by
        intro a n h1 h2
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨h1, h2⟩
      have hio : ∀ a, a = cfg.ioEOF ∨ a = cfg.ioEOF + 8 → (mN.writeLE (s.sp.toNat - 16) 8 zv.toNat).readLE a 8 = s.mem.readLE a 8 := by
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
      janus_run [hs_ra, hs_fp, hnz']
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
      refine ⟨(fun v' hv' => (by rw [hv] at hv'; cases hv')), fun _ => ⟨?_, ?_⟩, (fun h => (by rw [hv] at h; cases h)),
        (fun _ _ h => (by rw [hv] at h; cases h)), hFr⟩
      · rw [c0]; exact hio _ (Or.inl rfl)
      · rw [c1]; exact hio _ (Or.inr rfl)
    · -- ErrBig256Range
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, hE3, hInit, -, -, -, -, -, -, -, -, -⟩ := hpreC
      have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
        have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [hsp48] at k5 k6
      have hs_fp : s'.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
        rw [show s.sp.toNat - 56 = s.sp.toNat - 48 - 8 by omega, k5, show s.sp.toNat - 48 - 8 = s.sp.toNat - 56 by omega, hS_fp]
        exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
      have hs_ra : s'.mem.readLE (s.sp.toNat - 48) 8 = ret := by
        rw [k6, hS_ra, hretlt]
      have hoS : ∀ a n, a + n ≤ lo ∨ s.sp.toNat - 16 ≤ a → a + n ≤ zv.toNat ∨ zv.toNat + 32 ≤ a →
          Outside a n [(lo, s.sp.toNat - 16), (zv.toNat, zv.toNat + 32)] := by
        intro a n h1 h2
        simp only [outside_cons, outside_nil, and_true]
        exact ⟨h1, h2⟩
      have hio : ∀ a, a = cfg.errBig ∨ a = cfg.errBig + 8 → (mN.writeLE (s.sp.toNat - 16) 8 zv.toNat).readLE a 8 = s.mem.readLE a 8 := by
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
      janus_run [hs_ra, hs_fp, hnz']
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
      refine ⟨(fun v' hv' => (by rw [hv] at hv'; cases hv')), (fun h => (by rw [hv] at h; cases h)), fun _ => ⟨?_, ?_⟩,
        (fun _ _ h => (by rw [hv] at h; cases h)), hFr⟩
      · rw [c0]; exact hio _ (Or.inl rfl)
      · rw [c1]; exact hio _ (Or.inr rfl)
    · -- syntax error
      have hsp48 : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by
        have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [hsp48] at k5 k6
      have hs_fp : s'.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
        rw [show s.sp.toNat - 56 = s.sp.toNat - 48 - 8 by omega, k5, show s.sp.toNat - 48 - 8 = s.sp.toNat - 56 by omega, hS_fp]
        exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
      have hs_ra : s'.mem.readLE (s.sp.toNat - 48) 8 = ret := by
        rw [k6, hS_ra, hretlt]
      have hnz' : ¬ (s'.regs 0).toNat = 0 := by
        rw [c0]; decide
      have hnum : ¬ cfg.numErrItab = 0 := by decide
      have hnz'' : ¬ (BitVec.ofNat 64 cfg.numErrItab).toNat = 0 := by decide
      janus_run [hs_ra, hs_fp, hnz', hnz'', hnum]
      have hFr : MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]) := by
        refine hF.trans cMF ?_
        intro a n h
        simp only [outside_append] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine ⟨by rw [outside_append]; exact ⟨h1, h3⟩, ?_⟩
        have h4 := InRanges.apart hInR h1
        unfold Apart at h4
        simp only [outside_append, outside_cons, outside_nil, and_true] at h3 ⊢
        exact ⟨⟨h1, h2⟩, by omega, h4⟩
      refine ⟨(fun v' hv' => (by rw [hv] at hv'; cases hv')), (fun h => (by rw [hv] at h; cases h)),
        (fun h => (by rw [hv] at h; cases h)), fun _ _ _ => trivial, hFr⟩

end Fv256.Arm64.FromDecimal
