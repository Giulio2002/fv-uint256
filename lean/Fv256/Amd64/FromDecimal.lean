import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec

/-!
# `uint256.FromDecimal(decimal string) (*Int, error)` (amd64)   [DRAFT: conditional on the `SetFromDecimal` summary]

`var z Int; if err := z.SetFromDecimal(decimal); err != nil { return nil, err }; return &z, nil`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.FromDecimal

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
  fnStr := Extracted.dataAddr.«.rodata#3d2a826c»
  mallocgc := Extracted.program.contractAddr "runtime.mallocgc"
  memmove := Extracted.program.contractAddr "runtime.memmove"
  newobject := Extracted.program.contractAddr "runtime.newobject"
  wb1 := Extracted.program.contractAddr "runtime.gcWriteBarrier1"
  wb2 := Extracted.program.contractAddr "runtime.gcWriteBarrier2"

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

open Fv256.C in
/-- precondition of `FromDecimal(s)` (string pointer in `RAX`, length in `RBX`): `FromDecimalSpec.PreC` plus the rodata -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Amd64.FromDecimalSpec.PreC cfg R R2 T b L lo hi Extracted.dataAddr.«type:uint256.Int#33f34945» pS nS s ∧
  Extracted.program.DataLoaded s.mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Fv256.C in
theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    Ensures (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun s s' =>
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof →
          s'.regs 0 = 0 ∧ (s'.regs 3).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.ioEOF + 8) 8) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range →
          s'.regs 0 = 0 ∧ (s'.regs 3).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.errBig + 8) 8) ∧
        (∀ lo' len', decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' →
          s'.regs 0 = 0 ∧ s'.regs 3 = BitVec.ofNat 64 cfg.numErrItab) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hpreC, hdl⟩ := hpre
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
      ((s.regs 4).toNat + 8) 8 pS.toNat).writeLE ((s.regs 4).toNat - 48) 8 4932933) [(lo, hi)] := by
    refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)
  have hF1 : MemFrame s.mem mN (R.rt ++ [(lo, hi)]) := by
    refine hM0.trans hMF ?_
    intro a n h
    exact Fv256.Amd64.FromDecimalSpec.outside_sub_stack R.rt lo hi _ a n hlo hhi h
  have hF : MemFrame s.mem ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4932953)
      (R.rt ++ [(lo, hi)]) :=
    (hF1.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hInv' : R.inv (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) (s.regs 14).toNat
      (view R.rt (L ++ [(zv.toNat, zv.toNat + 32)])
        ((mN.writeLE ((s.regs 4).toNat - 16) 8 zv.toNat).writeLE ((s.regs 4).toNat - 48) 8 4932953)) := by
    refine RtInv.inv_frame' (ws := [((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8), ((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)])
      ((MemFrame.of_writeLE mN _ (r := ((s.regs 4).toNat - 16, (s.regs 4).toNat - 16 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)).writeLE _
        (r := ((s.regs 4).toNat - 48, (s.regs 4).toNat - 48 + 8)) (by simp) (Nat.le_refl _) (Nat.le_refl _)) ?_ hInvM
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    left
    rcases hr with rfl | rfl <;> exact Outside.of_sub hr9 (by omega) (by simp only; omega)
  refine Reaches.call (Summary.withExit (hsfd (b - 32) (L ++ [(zv.toNat, zv.toNat + 32)]) lo ((s.regs 4).toNat - 16) zv pS nS) hret) ?_ ?_ ?_
  · first | rfl | decide
  · refine Fv256.Amd64.FromDecimalSpec.toppre_of_call cfg hpreC (hi3 := (s.regs 4).toNat - 16) (by omega) (Nat.le_refl _) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply])
      (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp) (by simpa using h_df) ?_ hF hInR hApL hAcc (by omega) hInv'
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    decide
  · intro s' hr hq
    sorry

end Fv256.Amd64.FromDecimal
