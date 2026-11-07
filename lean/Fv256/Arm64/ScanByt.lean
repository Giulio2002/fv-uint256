import Extracted
import Fv256.Arm64.ScanSpec
import Fv256.Arm64.ScanCall
import Fv256.Arm64.ScanByt0
import Fv256.Arm64.ScanSciBase
import Fv256.Arm64.ScanSci

/-!
# `Scan` (arm64), the `[]byte` case: `string(b)` by the live `runtime.slicebytetostring`, then `scanScientificFromString`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSpec Fv256.Arm64.ScanCall
open Fv256.Arm64.ScanByt0

namespace Fv256.Arm64.ScanByt

abbrev scanEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Scan"
abbrev tyByt : Nat := Extracted.dataAddr.«type:[]uint8#7efbbf65»
abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

set_option maxRecDepth 100000 in
set_option janus.callRegions true in
theorem byt_call (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst dw : BitVec 64) (s S1 : State) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (hsal : s.sp.toNat % 16 = 0)
    (hpre : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s)
    (hpc : S1.pc = BitVec.ofNat 64 sbAddr) (hx0 : S1.regs 0 = s.sp - 40#64) (hx1 : S1.regs 1 = hdrP s dw)
    (hx2 : S1.regs 2 = hdrN s dw) (hsp : S1.sp = s.sp - 80#64) (h28 : S1.regs 28 = s.regs 28)
    (h29 : S1.regs 29 = s.sp - 88#64) (h18 : S1.regs 18 = s.regs 18) (h30 : S1.regs 30 = 753832#64)
    (hF : MemFrame s.mem S1.mem [(lo, hi)]) (hreg : S1.mem.regions = s.mem.regions)
    (hfp : S1.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S1.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat)
    (hdst : S1.mem.readLE (s.sp.toNat + 8) 8 = dst.toNat)
    (hdl : Extracted.program.DataLoaded S1.mem)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S1 (fun s' => True) := by
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hibuf, hiwin, -, -⟩ := hpre
  have hbufA : s.sp.toNat - 40 = 0 ∨ s.sp.toNat - 40 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 40) 32 true = true :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub _ (by rw [← hF.accessible]; exact e5) (Or.inr rfl) (by omega) (by omega)⟩
  have hw1 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 32 ≤ (hdrP s dw).toNat := by omega
  have hw2 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 80 - 4096 ∨ s.sp.toNat - 80 - 8 ≤ (hdrP s dw).toNat := by omega
  have hw3 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ s.sp.toNat - 80 + 8 ∨ s.sp.toNat - 80 + 8 + 24 ≤ (hdrP s dw).toNat := by omega
  janus_data hdl [haccW]
  janus_run (budget := 3000000) [hbufA, hw1, hw2, hw3, hpc, hx0, hx1, hx2, hsp, h28, h29, h30, haccW, hg4096, hinv', e13', hLs] until [sciEntry] calls [hsb]
  all_goals trace_state
  all_goals sorry

set_option maxRecDepth 100000 in
theorem scan_byt (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 scanEntry)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = tw) (h2 : s.regs 2 = dw) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (h48 : hi ≤ 2 ^ 48) (hsal : s.sp.toNat % 16 = 0) (hg : GuardOK s 80)
    (htw : tw.toNat = tyByt) (hdw : Ptr s.mem dw 24 false) (hdwW : dw.toNat + 24 ≤ lo ∨ hi ≤ dw.toNat)
    (hpre : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s)
    (hdl : Extracted.program.DataLoaded s.mem) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s (fun s' => True) := by
  janus_eval_nat h_sc : scanEntry
  janus_eval_nat h_ty : tyByt
  janus_eval_nat h_sb : sbAddr
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
  all_goals trace_state
  all_goals sorry

end Fv256.Arm64.ScanByt
