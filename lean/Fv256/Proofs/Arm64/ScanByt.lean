import Extracted
import Fv256.Proofs.Arm64.ScanSpec
import Fv256.Proofs.Arm64.ScanCall
import Fv256.Proofs.Arm64.ScanByt0
import Fv256.Proofs.Arm64.ScanByt1
import Fv256.Proofs.Arm64.ScanSciBase
import Fv256.Proofs.Arm64.ScanSci

/-!
# `Scan` (arm64), the `[]byte` case: `string(b)` by the live `runtime.slicebytetostring`, then `scanScientificFromString`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSpec Fv256.Arm64.ScanCall
open Fv256.Arm64.ScanByt0 Fv256.Arm64.ScanByt1

namespace Fv256.Arm64.ScanByt

abbrev scanEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Scan"
abbrev tyByt : Nat := Extracted.dataAddr.«type:[]uint8#7efbbf65»
abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

set_option maxRecDepth 100000 in
theorem byt_sci (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst dw r0 r1 : BitVec 64) (s S1 S2 : State) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (hsal : s.sp.toNat % 16 = 0)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hpre : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s) (hpg : PagesB R stAddr lo hi s.mem)
    (hF1 : MemFrame s.mem S1.mem [(lo, hi)]) (hdl1 : Extracted.program.DataLoaded S1.mem)
    (hreg1 : S1.mem.regions = s.mem.regions) (hreg2 : S2.mem.regions = S1.mem.regions)
    (hmf : MemFrame S1.mem S2.mem (R.rt ++ [(s.sp.toNat - 80 - 4096, s.sp.toNat - 80 - 8),
      (s.sp.toNat - 80 + 8, s.sp.toNat - 80 + 8 + 24)] ++
      if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hsoa : (r1.toNat = (strBytes S1.mem (hdrP s dw).toNat (hdrN s dw).toNat).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
        (0 < r1.toNat → s.mem.accessible r0.toNat r1.toNat false = true) ∧
        strBytes S2.mem r0.toNat r1.toNat = strBytes S1.mem (hdrP s dw).toNat (hdrN s dw).toNat) ∧
      StrAt R.rt (s.sp.toNat - 40) stAddr (hdrP s dw).toNat r1.toNat r0.toNat S1.mem)
    (hlf : LiveFrame S1.mem S2.mem L (if s.sp.toNat - 40 = 0 then [] else [(s.sp.toNat - 40, s.sp.toNat - 40 + 32)]))
    (hfr : FreshFrom (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L)
    (hinv : R.inv (b - roundupsize (hdrN s dw).toNat true)
      (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (s.regs 28).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (s.sp.toNat - 40 = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) S2.mem))
    (hpc : S2.pc = 754032#64) (hr0 : S2.regs 0 = dst) (hr1 : S2.regs 1 = r0) (hr2 : S2.regs 2 = r1)
    (hsp2 : S2.sp = s.sp - 80#64) (hr28 : S2.regs 28 = s.regs 28) (hr18 : S2.regs 18 = s.regs 18)
    (hr30 : S2.regs 30 = 753848#64)
    (hfp : S1.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S1.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat)
    (hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S2
      (fun s' => Kept s s' ∧ ScanStrPost cfg R R2 L R.rt lo hi dst (hdrP s dw) (hdrN s dw) s s') := by
  have h30a2 : (S2.regs 30).toNat % 4 = 0 := by rw [hr30]; decide
  have h30b2 : (S2.regs 30).toNat < 2 ^ 48 := by rw [hr30]; decide
  obtain ⟨hP0, hbytes, hF⟩ := byt_pre0 cfg hpre hpg hlo hhi hF1 hdl1 hreg2 hmf hsoa hlf hfr hinv hr0 hr1 hr2 hsp2 hr28 h30a2 h30b2
  have hn : r1.toNat = (hdrN s dw).toNat := by rw [hsoa.1.1]; simp
  have hbne : s.sp.toNat - 40 ≠ 0 := by omega
  have hr1' : r1 = hdrN s dw := BitVec.eq_of_toNat_eq hn
  have hsp80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
    have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hS2sp : S2.sp.toNat = s.sp.toNat - 80 := by rw [hsp2, hsp80]
  refine ReachesRet.call (Summary.regions (sci_summary impl R R2 T _ _ lo _ dst r0 (hdrN s dw) hsfd hexp hmo hibs))
    (by rw [hpc]; first | rfl | decide) hP0 ?_
  intro S3 hpc3 ⟨hpost, hreg3⟩
  have hpost' := hpost
  obtain ⟨k1, k2, k3, k4, k5, k6, -⟩ := hpost
  have hS3sp : S3.sp = s.sp - 80#64 := by rw [k1, hsp2]
  have hra : S3.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat := by
    have e : s.sp.toNat - 80 = S2.sp.toNat := by omega
    rw [e, k6, ← e]
    rw [hmf.readLE _ _ (by
      have hw : Outside lo (hi - lo) R.rt := hpre.2.1.2.2.2.2.2.2.2.2.1
      simp only [if_neg hbne, outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub hw (by omega) (by omega), by omega, by omega⟩, by omega⟩), ← hlr]
  have hfp3 : S3.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat := by
    have e : s.sp.toNat - 88 = S2.sp.toNat - 8 := by omega
    rw [e, k5, ← e]
    rw [hmf.readLE _ _ (by
      have hw : Outside lo (hi - lo) R.rt := hpre.2.1.2.2.2.2.2.2.2.2.1
      simp only [if_neg hbne, outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub hw (by omega) (by omega), by omega, by omega⟩, by omega⟩), ← hfp]
  have hacc3 : S3.mem.accessible (s.sp.toNat - 88) 120 true = true := by
    have e : S3.mem.regions = s.mem.regions := by rw [hreg3, hreg2, hreg1]
    unfold Janus.Arm64.Memory.accessible at hacc2 ⊢
    rw [e]; exact hacc2
  have hacc3' : S3.mem.accessible (s.sp.toNat - 88) 16 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hpc3' : S3.pc = BitVec.ofNat 64 753848 := by rw [hpc3]; exact hr30
  have h30b' : (s.regs 30).toNat < 2 ^ 56 := by omega
  janus_run [hpc3', hS3sp, hra, hfp3, hsal, hacc3, hacc3', Fv256.Arm64.ScanSci.ofn, h30b', h30a]
  refine ⟨⟨by simp, by simp [setReg_apply], by simp [setReg_apply, k3, hr28], by simp [setReg_apply, k4, hr18]⟩, ?_⟩
  refine strpost_congr cfg (S3 := S3) rfl (by simp [setReg_apply]) (by simp [setReg_apply]) ?_
  exact byt_post cfg hpre hlo hhi hF hbytes (by have := hsoa.1.2.1; omega) (fun r hr => List.mem_append_left _ hr)
    (by omega) hpost'

set_option maxRecDepth 100000 in
set_option janus.callRegions true in
theorem byt_call (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst dw : BitVec 64) (s S1 : State) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (hsal : s.sp.toNat % 16 = 0)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hpre : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s) (hpg : PagesB R stAddr lo hi s.mem)
    (hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true)
    (hpc : S1.pc = BitVec.ofNat 64 sbAddr) (hx0 : S1.regs 0 = s.sp - 40#64) (hx1 : S1.regs 1 = hdrP s dw)
    (hx2 : S1.regs 2 = hdrN s dw) (hsp : S1.sp = s.sp - 80#64) (h28 : S1.regs 28 = s.regs 28)
    (h29 : S1.regs 29 = s.sp - 88#64) (h18 : S1.regs 18 = s.regs 18) (h30 : S1.regs 30 = 753832#64)
    (hF : MemFrame s.mem S1.mem [(lo, hi)]) (hreg : S1.mem.regions = s.mem.regions)
    (hfp : S1.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S1.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat)
    (hdst : S1.mem.readLE (s.sp.toNat + 8) 8 = dst.toNat)
    (hdl : Extracted.program.DataLoaded S1.mem)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S1
      (fun s' => Kept s s' ∧ ScanStrPost cfg R R2 L R.rt lo hi dst (hdrP s dw) (hdrN s dw) s s') := by
  have hspS : S1.sp.toNat = s.sp.toNat - 80 := by
    have := s.sp.isLt; rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hpre' := hpre
  obtain ⟨hMod, hEnv, hok, hcost, -⟩ := hpre'
  have hEnvS : Env cfg R R2 T b L lo hi S1 :=
    Env.frame0 hMod.1 hEnv ⟨by have := hEnv.1; omega, by have := hEnv.2.1; omega, by have := hEnv.2.2.2.1; omega⟩ h28 hF (by omega)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, hinv, e18⟩ := hEnvS
  have haccW : S1.mem.accessible (S1.sp.toNat - 4096) 4128 true = true :=
    Janus.Arm64.Memory.accessible_sub _ e5 (Or.inr rfl) (by omega) (by omega)
  have hg4096 : GuardOK S1 4096 := ⟨e6, e7, by omega⟩
  have e13' : (s.regs 28).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 28).toNat + 16 := by rw [h28] at e13; exact e13
  have hinv' : R.inv b L (s.regs 28).toNat (view R.rt L S1.mem) := by rw [h28] at hinv; exact hinv
  have hLs : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 80 - 4096 ∨ s.sp.toNat - 80 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 80 + 8 ∨ s.sp.toNat - 80 + 8 + 24 ≤ r.1) := by
    intro r hr
    have := e18 r hr
    simp only [outside_cons, outside_nil, and_true] at this
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hibuf, hiwin, -, -⟩ := id hpre
  have hbufA : s.sp.toNat - 40 = 0 ∨ s.sp.toNat - 40 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 40) 32 true = true :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub _ (by rw [← hF.accessible]; exact e5) (Or.inr rfl) (by omega) (by omega)⟩
  have hw1 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 32 ≤ (hdrP s dw).toNat := by omega
  have hw2 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 80 - 4096 ∨ s.sp.toNat - 80 - 8 ≤ (hdrP s dw).toNat := by omega
  have hw3 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 80 + 8 ∨ s.sp.toNat - 80 + 8 + 24 ≤ (hdrP s dw).toNat := by omega
  have hw4 : Outside (s.sp.toNat - 80 - 4096) (s.sp.toNat - 80 - 8 - (s.sp.toNat - 80 - 4096)) R.rt :=
    Outside.of_sub e9 (by omega) (by omega)
  have hw5 : Outside (s.sp.toNat - 80 + 8) 24 R.rt := Outside.of_sub e9 (by omega) (by omega)
  have hwr : Outside lo (hi - lo) R.rt := e9
  have hbne : s.sp.toNat - 40 ≠ 0 := by omega
  have hpreH := Hide.mk hpre
  have hpgH := Hide.mk hpg
  clear hpre hpg hEnv hMod hcost hibuf hiwin e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e18 hinv
  janus_run (budget := 3000000) [hw4, hw5, hok, hbufA, hw1, hw2, hw3, hpc, hx0, hx1, hx2, hsp, h28, h29, h30, haccW, hg4096, hinv', e13', hLs] until [sciEntry] calls [hsb]
  have hpre := hpreH.get
  have hpg := hpgH.get
  refine byt_sci impl R R2 T b L lo hi dst dw _ _ s S1 _ hlo hhi hsal h30a h30b hpre hpg hF hdl hreg (by janus_assumption) (by janus_assumption) (by janus_assumption) (by janus_assumption) (by janus_assumption)
    (by janus_assumption) ?hpc ?hr0 ?hr1 ?hr2 ?hsp2 ?hr28 ?hr18 ?hr30 hfp hlr hacc2 hsfd hexp hmo hibs
  case hpc => rfl
  case hr0 =>
    janus_grab 4096 as hmf0
    have e := hmf0.readLE (s.sp.toNat + 8) 8 (by
      simp only [if_neg hbne, outside_append, outside_cons, outside_nil, and_true]
      refine ⟨⟨Outside.of_sub hwr (by omega) (by omega), by omega, by omega⟩, by omega⟩)
    simp only [setReg_apply, reduceIte]
    simp
    rw [e, hdst, Fv256.Arm64.ScanSci.ofn]
  case hr1 => simp [setReg_apply]
  case hr2 => simp [setReg_apply]
  case hsp2 => rfl
  case hr28 => simp [callRegs, setReg_apply, h28]
  case hr18 => simp [callRegs, setReg_apply, h18]
  case hr30 => simp [setReg_apply]

set_option maxRecDepth 100000 in
theorem scan_byt (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 scanEntry)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = tw) (h2 : s.regs 2 = dw) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (h48 : hi ≤ 2 ^ 48) (hsal : s.sp.toNat % 16 = 0) (hg : GuardOK s 80)
    (htw : tw.toNat = tyByt) (hdw : Ptr s.mem dw 24 false) (hdwW : dw.toNat + 24 ≤ lo ∨ hi ≤ dw.toNat)
    (hpre : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s) (hpg : PagesB R stAddr lo hi s.mem)
    (hdl : Extracted.program.DataLoaded s.mem) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s
      (fun s' => Kept s s' ∧ ScanStrPost cfg R R2 L R.rt lo hi dst (hdrP s dw) (hdrN s dw) s s') := by
  janus_eval_nat h_sc : scanEntry
  janus_eval_nat h_ty : tyByt
  rw [h_sc] at hpc
  have hpre' := hpre
  obtain ⟨hMod, hEnv, -⟩ := hpre'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv'
  have hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  have htw' : s.regs 1 = BitVec.ofNat 64 tyByt := by
    rw [h1]; apply BitVec.eq_of_toNat_eq; rw [htw]; simp only [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by rw [h_ty]; decide)).symm
  rw [h_ty] at htw'
  janus_data hdl [hr5]
  janus_run [hpc, h0, h1, h2, hg, hdw, htw, h_ty, hacc2, hsal, htw'] until [sbAddr]
  case h =>
    refine byt_call impl R R2 T b L lo hi dst dw s _ hlo hhi hsal h30a h30b hpre hpg hacc2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsb hsfd hexp hmo hibs
    · rfl
    · simp [setReg_apply]
    · simp [setReg_apply, hdrP]
    · simp [setReg_apply, hdrN]
    · rfl
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · janus_frame
    · simp only [Janus.Arm64.Memory.regions_writeLE]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Fv256.Arm64.ScanSci.mod64]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Fv256.Arm64.ScanSci.mod64]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Fv256.Arm64.ScanSci.mod64]
    · refine dl_frame (ws := [(lo, hi)]) hdl (by janus_frame) (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact hr5

end Fv256.Arm64.ScanByt
