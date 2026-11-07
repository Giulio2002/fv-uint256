import Extracted
import Fv256.Arm64.ScanSpec
import Fv256.Arm64.ScanCall
import Fv256.Arm64.ScanSciBase
import Fv256.Arm64.ScanSci

/-!
# `Scan` (arm64), the `string` case: the type switch, the call of `scanScientificFromString`, the return
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSci Fv256.Arm64.ScanSpec Fv256.Arm64.ScanCall

namespace Fv256.Arm64.ScanStr

/-- the `Scan` entry address -/
abbrev scanEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Scan"
abbrev tyStr : Nat := Extracted.dataAddr.«type:string#f88732b8»

theorem str_tail (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s S S3 : State) (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (hsal : s.sp.toNat % 16 = 0) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (htop : TopPre0 cfg R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)))
    (hsp : S.sp = s.sp - 80#64) (h28 : S.regs 28 = s.regs 28) (h18 : S.regs 18 = s.regs 18) (h29 : S.regs 29 = s.sp - 88#64)
    (h30 : S.regs 30 = 753900#64)
    (hfp : S.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat)
    (hlr : S.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat)
    (hF : MemFrame s.mem S.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) (hreg : S.mem.regions = s.mem.regions)
    (hacc : s.mem.accessible (s.sp.toNat - 88) 120 true = true)
    (hpc3 : S3.pc = S.regs GoABI.regLR) (hreg3 : S3.mem.regions = S.mem.regions)
    (hpost : SciPost cfg R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) S S3) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3
      (fun s' => Kept s s' ∧ ScanStrPost cfg R R2 L [] lo hi dst (hdrP s dw) (hdrN s dw) s s') := by
  have hpost' := hpost
  obtain ⟨k1, k2, k3, k4, k5, k6, -⟩ := hpost
  have hsp80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
    have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hSsp : S.sp.toNat = s.sp.toNat - 80 := by rw [hsp, hsp80]
  have hS3sp : S3.sp = s.sp - 80#64 := by rw [k1, hsp]
  have hra : S3.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat := by
    rw [← hlr, ← hSsp]; exact k6
  have hfp' : S3.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat := by
    rw [← hfp]
    have : s.sp.toNat - 88 = S.sp.toNat - 8 := by omega
    rw [this]; exact k5
  have hacc3 : S3.mem.accessible (s.sp.toNat - 88) 120 true = true := by
    have e : S3.mem.regions = s.mem.regions := by rw [hreg3, hreg]
    unfold Janus.Arm64.Memory.accessible at hacc ⊢
    rw [e]; exact hacc
  have hacc3' : S3.mem.accessible (s.sp.toNat - 88) 16 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (Nat.le_refl _) (by omega)
  have hpc3' : S3.pc = BitVec.ofNat 64 753900 := by rw [hpc3]; exact h30
  have h30b' : (s.regs 30).toNat < 2 ^ 56 := by omega
  janus_run [hpc3', hS3sp, hra, hfp', hsal, hacc3, hacc3', ofn, h30b', h30a]
  have htop' := htop
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hP48, hPW, hPZ, -⟩ := htop'
  obtain ⟨⟨io1, io2⟩, ⟨er1, er2⟩, ⟨sy1, sy2⟩⟩ := frame_consts cfg htop (S := S) hF
  have hsp3 : S3.sp = s.sp - 80#64 := by rw [k1, hsp]
  refine ⟨⟨by simp, by simp [setReg_apply], by simp [setReg_apply, k3, h28], by simp [setReg_apply, k4, h18]⟩, ?_⟩
  refine strpost_congr cfg (S3 := S3) rfl (by simp [setReg_apply]) (by simp [setReg_apply]) ?_
  exact str_post cfg (W := []) hF (fun a n h => by simp only [outside_append, List.nil_append] at h ⊢; exact h.2) (fun k hk => hF.readLE _ _ (str_out2 hPW hPZ hk)) hP48 hP48 io1 io2 er1 er2 sy1 sy2 hpost'

theorem scan_str (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.pc = BitVec.ofNat 64 scanEntry)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = tw) (h2 : s.regs 2 = dw) (hlo : lo + 4720 ≤ s.sp.toNat)
    (hhi : s.sp.toNat + 32 ≤ hi) (h48 : hi ≤ 2 ^ 48) (hsal : s.sp.toNat % 16 = 0) (hg : GuardOK s 80)
    (htw : tw.toNat = tyStr) (hdw : Ptr s.mem dw 16 false) (hdwW : dw.toNat + 16 ≤ lo ∨ hi ≤ dw.toNat)
    (htop : TopPre0 cfg R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)))
    (hinit : InitDone cfg R2 s.mem) (hpage : Fv256.IndexByte.PageReadable s.mem (hdrP s dw).toNat (hdrN s dw).toNat)
    (hdl : Extracted.program.DataLoaded s.mem) (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s
      (fun s' => Kept s s' ∧ ScanStrPost cfg R R2 L [] lo hi dst (hdrP s dw) (hdrN s dw) s s') := by
  janus_eval_nat h_sc : scanEntry
  janus_eval_nat h_ty : tyStr
  rw [h_sc] at hpc
  have htop' := htop
  obtain ⟨-, -, -, hMod, hEnv, -⟩ := htop'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv'
  have hr5' : s.mem.accessible lo (hi - lo) true = true := hr5
  have hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hr5' (Or.inr rfl) (by omega) (by omega)
  have htw' : s.regs 1 = BitVec.ofNat 64 tyStr := by
    rw [h1]; apply BitVec.eq_of_toNat_eq; rw [htw]; simp only [BitVec.toNat_ofNat]; exact (Nat.mod_eq_of_lt (by rw [h_ty]; decide)).symm
  rw [h_ty] at htw'
  janus_data hdl [hr5']
  janus_run [hpc, h0, h1, h2, hg, hdw, htw, h_ty, hacc2, hsal, htw'] until [sciEntry]
  case h =>
    have hsp80 : (s.sp - 80#64).toNat = s.sp.toNat - 80 := by
      have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine ReachesRet.call (Summary.regions (sci_summary impl R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) hsfd hexp hmo hibs))
      (by first | rfl | decide) ?_ ?_
    · unfold Pre0
      refine str_pre0 cfg htop h30a h30b hinit hpage hdl ?hF ?hreg ?hal ?h0 ?h1 ?h2 ?h30a' ?h30b' ?h28 ?hlo' ?hhi'
      case hF => janus_frame
      case hreg => simp only [Janus.Arm64.Memory.regions_writeLE]
      case hal => rw [hsp80]; omega
      case h0 => simp [setReg_apply, h0]
      case h1 => simp [setReg_apply, hdrP]
      case h2 => simp [setReg_apply, hdrN]
      case h30a' => simp [setReg_apply]
      case h30b' => simp [setReg_apply]
      case h28 => simp [setReg_apply]
      case hlo' => rw [hsp80]; omega
      case hhi' => rw [hsp80]; omega
    · intro S3 hpc3 ⟨hpost, hreg3⟩
      refine str_tail impl R R2 T b L lo hi dst tw dw s _ S3 hlo hhi hsal h30a h30b htop ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hacc2 hpc3 hreg3 hpost
      · rfl
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
      · janus_frame
      · simp only [Janus.Arm64.Memory.regions_writeLE]
