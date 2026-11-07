import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.IbsA64
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.ScanSciSpec
import Fv256.Arm64.ScanSciBase
import Fv256.Arm64.ScanSciF1

/-!
# `(*uint256.Int).scanScientificFromString` (arm64): the summary `sci_summary` (internal to `Scan`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

theorem seg_post_ibs (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0) (S : State) (hfr : Fr lo dst pS nS s S)
    (hpc : S.pc = BitVec.ofNat 64 (sciEntry + 0x44)) (h30 : S.regs 30 = BitVec.ofNat 64 (sciEntry + 0x44))
    (hx0 : (S.regs 0).toNat = Fv256.IndexByte.indexOfNat (bytesAt s.mem pS.toNat) nS.toNat 101) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hEnv0 := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv0
  have hfr0 := hfr
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hfr
  have hSsp : S.sp.toNat = s.sp.toNat - 112 := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hr136 : S.mem.readLE (S.sp.toNat + 136) 8 = nS.toNat := by rw [hSsp, show s.sp.toNat - 112 + 136 = s.sp.toNat + 24 by omega]; exact fn
  have hr128 : S.mem.readLE (S.sp.toNat + 128) 8 = pS.toNat := by rw [hSsp, show s.sp.toNat - 112 + 128 = s.sp.toNat + 16 by omega]; exact fp
  have hr120 : S.mem.readLE (S.sp.toNat + 120) 8 = dst.toNat := by rw [hSsp, show s.sp.toNat - 112 + 120 = s.sp.toNat + 8 by omega]; exact fdst
  have hrfp : S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [hSsp, show s.sp.toNat - 112 - 8 = s.sp.toNat - 120 by omega]; exact ffp
  have hrlr : S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [hSsp]; exact fra
  have hacc : S.mem.accessible (S.sp.toNat - 8) 152 true = true := by
    rw [fmf.accessible]
    exact Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x44 = 754100 from by rw [h_sci]] at hpc h30
  have hx0e : (S.regs 0).toNat = (match Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat with | some i => i | none => 2 ^ 64 - 1) := by
    rw [hx0]; exact indexOf_eq_idxE _ _
  have hSal : S.sp.toNat % 16 = 0 := by omega
  have hpc' : S.pc = BitVec.ofNat 64 (sciEntry + 0x44) := by rw [h_sci]; simpa using hpc
  have h30' : S.regs 30 = BitVec.ofNat 64 (sciEntry + 0x44) := by rw [h_sci]; simpa using h30
  clear fsp
  have h28' : S.regs 28 = s.regs 28 := f28
  by_cases hnone : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = none
  · rw [hnone] at hx0e
    have hx : S.regs 0 = 18446744073709551615#64 := BitVec.eq_of_toNat_eq (by simpa using hx0e)
    have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
    janus_run [e1, hpc, hx, hr136, hr128, hr120, hacc, hrfp, hrlr, h28', h30, f28, hSal] until [sfdEntry]
    case h =>
      have hF : MemFrame s.mem S.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
        fmf.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega)
      refine ReachesRet.call (Summary.regions (hsfd b L lo (S.sp.toNat + 32) dst pS nS)) (by first | rfl | decide) ?_ ?_
      · refine call_pre cfg htop hF hSal (by omega) (Or.inl rfl) (by omega) (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩) hP48
          (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
          (by simp [setReg_apply, f28]) (by simp; omega) (by simp) hzR hzPr hzS hzg (by rw [fmf.accessible]; exact hzP.1) hzP.2
      · intro S3 hpc3 ⟨hpost, hreg3⟩
        have hpost' := hpost
        obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
        dsimp only at k1 k2 k3 k4 k5 k6
        have hra : S3.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat := by rw [k6]; exact hrlr
        have hfp' : S3.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [k5]; exact hrfp
        have hsi : (S.sp.toNat + 112) = s.sp.toNat := by rw [hSsp]; exact Nat.sub_add_cancel (Nat.le_trans (by omega) hlo)
        have hacc3 : S3.mem.accessible (S.sp.toNat - 8) 152 true = true := by
          have e : S3.mem.regions = S.mem.regions := hreg3
          unfold Janus.Arm64.Memory.accessible at hacc ⊢
          rw [e]; exact hacc
        have hacc3' : S3.mem.accessible (S.sp.toNat - 8) 8 false = true :=
          Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (by omega) (by omega)
        janus_run [hra, hfp', hSal, ofn, hacc3, hacc3']
        have hsp112 : S.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := s.sp.isLt; omega)
        have hbytes : decParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt S.mem pS.toNat) nS.toNat :=
          Fv256.I.decParse_congr _ _ _ (fun k hk => (fmf.readLE (pS.toNat + k) 1 (str_outside hPW hPZ (by omega) hhi k hk)).symm)
        have hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = decParse (bytesAt s.mem pS.toNat) nS.toNat := by
          rw [sci_none hn hnone]
        have hr28' : S3.regs 28 = s.regs 28 := by rw [k3, ← f28]; simp [setReg_apply]
        have hr18' : S3.regs 18 = s.regs 18 := by rw [k4, ← f18]; simp [setReg_apply]
        refine post_tail cfg htop hlo112 hfr0 (by omega) hpost' hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, hr28'])
          (by simp [setReg_apply, hr18']) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl hsci
  · obtain ⟨i, hidx⟩ := Option.ne_none_iff_exists'.mp hnone
    rw [hidx] at hx0e
    exact seg_found1 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn S hfr0 hpc' h30' i hidx hx0e

theorem seg_entry (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (hibs : Fv256.IndexByte.IbsLib64 (Extracted.program.link impl) ibsEntry)
    (s : State) (hpc : s.pc = BitVec.ofNat 64 sciEntry) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hEnv' := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18⟩ := hEnv'
  have hacc : s.mem.accessible (s.sp.toNat - 120) 152 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_eval_nat h_sci : sciEntry
  rw [h_sci] at hpc
  janus_run [hpc, h0, h1, h2, hacc, hr8, hr7, hr4, Nat.mod_eq_of_lt (show (s.regs 28).toNat + 16 < 2 ^ 64 by omega)] until [ibsEntry]
  case hq =>
    -- nS = 0 : `dst` cleared
    have hn0 : nS.toNat = 0 := by janus_assumption
    have hdst : Apart dst.toNat 32 (s.sp.toNat - 120) 152 := apart_win hzW (by omega) (by omega)
    clr
    unfold SciPost
    simp only [hn0, sci_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨0, rfl, ?_, ?_, ?_, ?_⟩⟩
    · trivial
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp (disch := omega) only [val256, Fv256.Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    · janus_frame
  case h =>
    clr
    refine ReachesRet.call (Summary.regions (hibs pS nS 101)) (by first | rfl | decide) ?_ ?_
    · refine ⟨by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], by simp [setReg_apply], ?_⟩
      exact pr_frame (ws := [(lo, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 32), (dst.toNat, dst.toNat + 32)]) (by janus_frame) hpage
    · intro S2 hpc2 ⟨⟨hx0, hmem, hsp, h18, h28, h29, h30⟩, hreg⟩
      dsimp only at hpc2 hx0 hmem hsp h18 h28 h29 h30 hreg
      have hfr : Fr lo dst pS nS s S2 := by
        unfold Fr
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hsp]
        · rw [h28]; simp [setReg_apply]
        · rw [h18]; simp [setReg_apply]
        · rw [h29]; simp [setReg_apply]
        · rw [hmem]; janus_frame
        · rw [hreg]; simp
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
        · rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, mod64]
      have hbytes : ∀ k, k < nS.toNat → Fv256.IndexByte.bytesOf (S2.mem) pS.toNat k = bytesAt s.mem pS.toNat k := by
        intro k hk
        have := hfr.2.2.2.2.1.readLE (pS.toNat + k) 1 (str_outside hPW hPZ (by omega) hhi k hk)
        exact this
      rw [← hmem] at hx0
      have hx0' : (S2.regs 0).toNat = Fv256.IndexByte.indexOfNat (bytesAt s.mem pS.toNat) nS.toNat 101 := by
        rw [hx0]
        exact indexOfNat_congr _ _ _ _ hbytes
      have hbrn : ¬ nS.toNat = 0 := by janus_assumption
      refine seg_post_ibs impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ (by intro h; exact hbrn h) S2 hfr ?_ ?_ hx0'
      · rw [hpc2]; simp [setReg_apply, h_sci]
      · rw [h30]; simp [setReg_apply, h_sci]

end Fv256.Arm64.ScanSci
