import Extracted
import Fv256.Proofs.Arm64.ScanSpec
import Fv256.Proofs.Arm64.ScanCall
import Fv256.Proofs.Arm64.ScanSciBase

/-!
# `Scan` (arm64), the unsupported-type case: `errors.New("unsupported type")`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanCall

namespace Fv256.Arm64.ScanOther

abbrev scanEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Scan"
abbrev tyStr : Nat := Extracted.dataAddr.«type:string#f88732b8»
abbrev tyByt : Nat := Extracted.dataAddr.«type:[]uint8#7efbbf65»
abbrev tyErr : Nat := Extracted.dataAddr.«type:errors.errorString#8e8100b7»
abbrev newAddr : Nat := Extracted.program.contractAddr "runtime.newobject"

set_option maxRecDepth 100000 in
theorem unsup_data {m : Janus.Arm64.Memory} (hdl : Extracted.program.DataLoaded m) :
    ∀ k, k < 16 → m.readLE (968630 + k) 1 = unsupB k := by
  intro k hk
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Janus.Tactic.readLE_of_dataRead hdl (by decide)

set_option maxRecDepth 100000 in
theorem other_tail (impl : List Janus.Segment) (R : RtInv) (L : List (Nat × Nat)) (lo hi : Nat) (s S S4 : State) (w : BitVec 64)
    (blk : Nat) (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi) (hsal : s.sp.toNat % 16 = 0)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hdl : Extracted.program.DataLoaded S.mem) (hRW : ∀ r ∈ R.rt, S.mem.accessible r.1 (r.2 - r.1) true = true)
    (hpc4 : S4.pc = 753936#64) (hsp4 : S4.sp = s.sp - 80#64) (hx0 : S4.regs 0 = w) (hx1 : S4.regs 1 = 968630#64)
    (hx2 : S4.regs 2 = 16#64) (hx28 : S4.regs 28 = s.regs 28) (hx18 : S4.regs 18 = s.regs 18) (hx29 : S4.regs 29 = s.sp - 88#64)
    (hmf : MemFrame S.mem S4.mem (R.rt ++ [(s.sp.toNat - 80 - 4096, s.sp.toNat - 80 - 8), (s.sp.toNat - 80 + 8, s.sp.toNat - 80 + 8 + 8)]))
    (hin : InRanges w.toNat blk R.rt) (hap : ApartAll w.toNat blk L) (hblk : 16 ≤ blk)
    (hacc : S.mem.accessible w.toNat blk true = true) (hWrt : Outside lo (hi - lo) R.rt)
    (hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true)
    (hF : MemFrame s.mem S.mem [(lo, hi)]) (hreg4 : S4.mem.regions = S.mem.regions)
    (hlh : S.mem.accessible lo (hi - lo) true = true)
    (hfp : S.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S4
      (fun s' => Kept s s' ∧ s'.regs 0 = BitVec.ofNat 64 Extracted.dataAddr.«go:itab.*errors.errorString,error» ∧
        (∃ (blk ptr : Nat), s'.regs 1 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
          s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])) := by
  have hsp80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
    have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hacc4 : S4.mem.accessible w.toNat 16 true = true := by
    rw [hmf.accessible]; exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hw48 : w.toNat + 16 ≤ 2 ^ 48 := by have := Fv256.Arm64.ScanCall.acc_le48 hacc4; omega
  have hwo : ∀ a n, lo ≤ a → a + n ≤ hi → Outside a n R.rt := fun a n h1 h2 => Outside.of_sub hWrt h1 (by omega)
  have hfp4 : S4.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat := by
    rw [hmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hwo _ _ (by omega) (by omega), by omega, by omega⟩), hfp]
  have hlr4 : S4.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat := by
    rw [hmf.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      exact ⟨hwo _ _ (by omega) (by omega), by omega, by omega⟩), hlr]
  have haccS4 : S4.mem.accessible (s.sp.toNat - 88) 16 false = true := by
    rw [hmf.accessible, hF.accessible]
    exact Janus.Arm64.Memory.accessible_sub _ hacc2 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have h30b' : (s.regs 30).toNat < 2 ^ 56 := by omega
  have hdj := InRanges.disjoint hin (hwo (s.sp.toNat - 88) 16 (by omega) (by omega))
  try unfold Apart at hdj
  janus_run [hdj, hpc4, hsp4, hx0, hx1, hx2, hx28, hx18, hx29, hacc4, hw48, hfp4, hlr4, haccS4, hsp80, hsal, h30a, h30b', Fv256.Arm64.ScanSci.ofn]
  have hdl4 : Extracted.program.DataLoaded S4.mem := by
    refine dl_frame hdl hmf hreg4 (fun r hr => ?_)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | rfl | rfl
    · exact hRW r hr
    · exact Janus.Arm64.Memory.accessible_sub _ hlh (Or.inr rfl) (by omega) (by omega)
    · exact Janus.Arm64.Memory.accessible_sub _ hlh (Or.inr rfl) (by omega) (by omega)
  have hacc4' : S4.mem.accessible w.toNat 8 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc4 (Or.inr rfl) (Nat.le_refl _) (by omega)
  have hacc4'' : S4.mem.accessible (w.toNat + 8) 8 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc4 (Or.inr rfl) (by omega) (by omega)
  have hdlF : Extracted.program.DataLoaded ((S4.mem.writeLE w.toNat 8 968630).writeLE (w.toNat + 8) 8 16) := by
    refine Program.DataLoaded.writeLE (Program.DataLoaded.writeLE hdl4 hacc4') ?_
    simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact hacc4''
  have hw16 : InRanges w.toNat 16 R.rt := by obtain ⟨r, hr, h1, h2⟩ := hin; exact ⟨r, hr, h1, by omega⟩
  have hap16 : ApartAll w.toNat 16 L := by
    intro r hr
    have := hap r hr
    unfold Apart at this ⊢
    omega
  have hw8a : InRanges w.toNat 8 R.rt := by obtain ⟨r, hr, h1, h2⟩ := hw16; exact ⟨r, hr, h1, by omega⟩
  have hw8b : InRanges (w.toNat + 8) 8 R.rt := by obtain ⟨r, hr, h1, h2⟩ := hw16; exact ⟨r, hr, by omega, by omega⟩
  have hmf2 : MemFrame S4.mem ((S4.mem.writeLE w.toNat 8 968630).writeLE (w.toNat + 8) 8 16) R.rt :=
    (((MemFrame.refl S4.mem R.rt).writeLE_inRanges 968630 hw8a)).writeLE_inRanges 16 hw8b
  refine ⟨?_, by decide, ⟨w.toNat, 968630, by simp, hw16, hap16, ?_, ?_, ?_⟩, ?_⟩
  · simp [Kept, setReg_apply, hx28, hx18]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · exact unsup_data hdlF
  · refine hF.trans ((hmf.trans hmf2 (fun a n h => ⟨h, by simp only [outside_append] at h; exact h.1⟩))) (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    refine ⟨h.2, h.1, ?_, ?_⟩ <;> omega

set_option maxRecDepth 100000 in
set_option janus.callRegions true in
theorem other_call (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst : BitVec 64) (s S : State) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hMod : Mod cfg R R2 T L) (hEnv : Env cfg R R2 T b L lo hi s)
    (hok : R.ok newAddr [tyErr]) (hb : blockSize 16 false ≤ b)
    (hsp : S.sp = s.sp - 80#64) (h28 : S.regs 28 = s.regs 28) (h29 : S.regs 29 = s.sp - 88#64) (h18 : S.regs 18 = s.regs 18)
    (h30 : S.regs 30 = 753924#64) (hpc : S.pc = BitVec.ofNat 64 newAddr) (hr0 : S.regs 0 = BitVec.ofNat 64 tyErr)
    (hF : MemFrame s.mem S.mem [(lo, hi)]) (hreg : S.mem.regions = s.mem.regions)
    (hRW0 : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hfp : S.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat)
    (hdl : Extracted.program.DataLoaded S.mem)
    (hnew : NewobjectLiveContract (Extracted.program.link impl) newAddr 4096 R) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S
      (fun s' => Kept s s' ∧ s'.regs 0 = BitVec.ofNat 64 Extracted.dataAddr.«go:itab.*errors.errorString,error» ∧
        (∃ (blk ptr : Nat), s'.regs 1 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
          s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])) := by
  have hspS : S.sp.toNat = s.sp.toNat - 80 := by
    have := s.sp.isLt; rw [hsp]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hEnv' := hEnv
  obtain ⟨-, -, -, hsal, -⟩ := hEnv'
  have hEnvS : Env cfg R R2 T b L lo hi S :=
    Env.frame0 hMod.1 hEnv ⟨by omega, by omega, by omega⟩ h28 hF (by omega)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, hinv, e18⟩ := hEnvS
  have haccW : S.mem.accessible (S.sp.toNat - 4096) 4112 true = true :=
    Janus.Arm64.Memory.accessible_sub _ e5 (Or.inr rfl) (by omega) (by omega)
  have hg4096 : GuardOK S 4096 := ⟨e6, e7, by omega⟩
  have hok' : R.ok newAddr [(S.regs 0).toNat] := by
    rw [hr0]; simp only [BitVec.toNat_ofNat]; exact (by
      have : tyErr % 2 ^ 64 = tyErr := Nat.mod_eq_of_lt (by decide)
      rw [this]; exact hok)
  have e13' : (s.regs 28).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 28).toNat + 16 := by rw [h28] at e13; exact e13
  have hinv' : R.inv b L (s.regs 28).toNat (view R.rt L S.mem) := by rw [h28] at hinv; exact hinv
  have hb16 : 16 ≤ b := by have : blockSize 16 false = 16 := by decide
                           omega
  have hLs : ∀ r ∈ L, (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 80 - 4096 ∨ s.sp.toNat - 80 - 8 ≤ r.1) ∧
      (r.1 + (r.2 - r.1) ≤ s.sp.toNat - 80 + 8 ∨ s.sp.toNat - 80 + 8 + 8 ≤ r.1) := by
    intro r hr
    have := e18 r hr
    simp only [outside_cons, outside_nil, and_true] at this
    omega
  -- the descriptor is outside the callee's window (the contract's `Outside et 16 (calleeStack ..)`): it is rodata and the
  -- window is writable. One lemma (`outside_calleeStack_of_data`), stated while the context is still small.
  have hty : tyErr = 874688 := rfl
  have hot : Outside tyErr 16 (calleeStack S 4096 1) :=
    outside_calleeStack_of_data hdl (by decide) (by omega) haccW
  -- the same fact in the exact shape of the contract's precondition conjunct (so `janus_run` closes it by matching)
  have hot' : Outside (S.regs 0).toNat 16 (calleeStack S 4096 1) := by
    rw [hr0]; simp only [BitVec.toNat_ofNat, show tyErr % 2 ^ 64 = tyErr from Nat.mod_eq_of_lt (by decide)]; exact hot
  have htyo : 874704 ≤ s.sp.toNat - 80 - 4096 ∨ s.sp.toNat - 80 - 8 ≤ 874688 := by
    simp only [calleeStack, outside_cons, outside_nil, and_true, hty] at hot
    omega
  janus_data hdl [haccW]
  have hsz : dataReadD Extracted.program tyErr 8 = 16 := by decide
  have hnb : (dataReadD Extracted.program (tyErr + 8) 8 == 0) = false := by decide
  have hRW : ∀ r ∈ R.rt, S.mem.accessible r.1 (r.2 - r.1) true = true := by
    intro r hr; rw [hF.accessible]; exact hRW0 r hr
  have hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Janus.Arm64.Memory.accessible_sub _ (by have := hEnv.2.2.2.2.1; exact this) (Or.inr rfl) (by omega) (by omega)
  have hlh : S.mem.accessible lo (hi - lo) true = true := by rw [hF.accessible]; exact hEnv.2.2.2.2.1
  janus_run [hsz, hnb, hpc, hr0, hsp, h28, h29, h30, haccW, hg4096, hok', hinv', e13', hb16, hLs, htyo, hot'] until [0xb8110] calls [hnew.pos]
  refine other_tail impl R L lo hi s S _ _ _ hlo hhi hsal h30a h30b hdl hRW ?hpc4 ?hsp4 ?hx0 ?hx1 ?hx2 ?hx28 ?hx18 ?hx29 (by assumption) (by assumption) (by assumption) ?hblk ?hacc e9 hacc2 hF ?hreg4 hlh hfp hlr
  case hpc4 => simp
  case hsp4 => simp
  case hx0 => simp [callRegs, setReg_apply]
  case hx1 => simp [callRegs, setReg_apply]
  case hx2 => simp [callRegs, setReg_apply]
  case hx28 => simp [callRegs, setReg_apply, h28]
  case hx18 => simp [callRegs, setReg_apply, h18]
  case hx29 => simp [callRegs, setReg_apply, h29]
  case hblk => first | decide | (simp only [hsz, hnb]; decide)
  case hacc => rw [hF.accessible]; assumption
  case hreg4 => assumption


theorem scan_other (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 scanEntry)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = tw) (h2 : s.regs 2 = dw) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (h48 : hi ≤ 2 ^ 48) (hsal : s.sp.toNat % 16 = 0) (hg : GuardOK s 80)
    (htw0 : tw ≠ 0) (htwS : tw.toNat ≠ tyStr) (htwB : tw.toNat ≠ tyByt)
    (htacc : s.mem.accessible (tw.toNat + 16) 4 false = true) (htwW : tw.toNat + 16 + 4 ≤ lo ∨ hi ≤ tw.toNat + 16)
    (hMod : Mod cfg R R2 T L) (hEnv : Env cfg R R2 T b L lo hi s)
    (hok : R.ok cfg.newobject [tyErr]) (hb : blockSize 16 false ≤ b)
    (hRW0 : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hdl : Extracted.program.DataLoaded s.mem) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hnew : NewobjectLiveContract (Extracted.program.link impl) newAddr 4096 R) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s
      (fun s' => Kept s s' ∧ s'.regs 0 = BitVec.ofNat 64 Extracted.dataAddr.«go:itab.*errors.errorString,error» ∧
        (∃ (blk ptr : Nat), s'.regs 1 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
          s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])) := by
  janus_eval_nat h_sc : scanEntry
  janus_eval_nat h_ty : tyStr
  janus_eval_nat h_tb : tyByt
  janus_eval_nat h_te : tyErr
  janus_eval_nat h_na : newAddr
  rw [h_sc] at hpc
  rw [h_ty] at htwS
  rw [h_tb] at htwB
  have htw48 : tw.toNat + 16 < 2 ^ 64 := by have := Fv256.Arm64.ScanCall.acc_le48 htacc; omega
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv'
  have hok' : R.ok newAddr [tyErr] := by unfold cfg at hok; exact hok
  have hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_run [hpc, h0, h1, h2, hg, htacc, htw48, htwS, htwB, h_ty, h_tb, hacc2, hsal] until [newAddr]
  all_goals (
    refine other_call impl R R2 T b L lo hi dst s _ hlo hhi h30a h30b hMod hEnv hok' hb ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hRW0 ?_ ?_ ?_ hnew
    · rfl
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]; first | rfl | decide
    · simp [setReg_apply]; first | rfl | decide
    · janus_frame
    · simp only [Janus.Arm64.Memory.regions_writeLE]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Fv256.Arm64.ScanSci.mod64]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Fv256.Arm64.ScanSci.mod64]
    · refine dl_frame (ws := [(lo, hi)]) hdl (by janus_frame) (by simp only [Janus.Arm64.Memory.regions_writeLE]) (fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact hr5)
