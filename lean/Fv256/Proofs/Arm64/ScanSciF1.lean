import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SpecScan
import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Common.IbsA64
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.ScanSciSpec
import Fv256.Proofs.Arm64.ScanSciBase
import Fv256.Proofs.Arm64.ScanSciF2

/-!
# `scanScientificFromString` (arm64): the first `SetFromDecimal` call (on `s[:idx]`), idx found
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

theorem found2a (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v)
    (S3 : State) (hFr : Fr lo dst pS nS s S3) (hspill : S3.mem.readLE (S3.sp.toNat + 32) 8 = i)
    (hval : Janus.Spec.val256 S3.mem dst.toNat = v) (hx0z : S3.regs 0 = 0)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0x6c)) (hc1 : nS.toNat = i + 1) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x6c = 754140 from by rw [h_sci]] at hpc3
  clear fsp
  have h28' : S3.regs 28 = s.regs 28 := f28
  have hiv : (BitVec.ofNat 64 i).toNat = i := by simp [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  have hnS : nS = BitVec.ofNat 64 (i + 1) := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := nS.isLt; omega)
  have hd : nS - BitVec.ofNat 64 (i + 1) = 0 := by rw [hnS]; simp
  have e2 : (addSub (nS - BitVec.ofNat 64 i) 2#64 true).snd.z = false := by
    rw [cmp_z]; simp only [decide_eq_false_iff_not]
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    have := nS.isLt; omega
  janus_run [hpc3, hx0z, hr136, hr128, hr120, hspill, hacc, hrfp, hrlr, h28', f28, hSal, e2, hd, mask_zero] until [754228]
  case h =>
    refine found3 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn i hsome v hv (by omega) _
      (fr_of_eq hfr0 rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl) hval
      (by simp [h_sci]) ⟨fun _ => by simp [setReg_apply], fun h => absurd h (by omega)⟩ (by simp [setReg_apply, hd])

theorem found2c (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v)
    (S3 : State) (hFr : Fr lo dst pS nS s S3) (hspill : S3.mem.readLE (S3.sp.toNat + 32) 8 = i)
    (hval : Janus.Spec.val256 S3.mem dst.toNat = v) (hx0z : S3.regs 0 = 0)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0x6c))  (hc3 : i + 3 ≤ nS.toNat) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x6c = 754140 from by rw [h_sci]] at hpc3
  clear fsp
  have h28' : S3.regs 28 = s.regs 28 := f28
  have hiv : (BitVec.ofNat 64 i).toNat = i := by simp [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  have hadd : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := nS.isLt; omega
  have hmk : BitVec.ofNat 64 i + 1#64 &&& (0#64 - (nS - BitVec.ofNat 64 (i + 1))).sshiftRight 63 = BitVec.ofNat 64 i + 1#64 := by
    apply mask_pos
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
  have e2 : (addSub (nS - BitVec.ofNat 64 i) 2#64 true).snd.z = false := by
    rw [cmp_z]; simp only [decide_eq_false_iff_not]
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    have := nS.isLt; omega
  janus_run [hpc3, hx0z, hr136, hr128, hr120, hspill, hacc, hrfp, hrlr, h28', f28, hSal, e2, hmk] until [754228]
  case h =>
    refine found3 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn i hsome v hv (by omega) _
      (fr_of_eq hfr0 rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl) hval
      (by simp [h_sci]) ⟨fun h => absurd h (by omega), fun _ => by simp [setReg_apply, hadd]⟩ (by simp [setReg_apply])

theorem found2b_ldrb (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v) (hc2 : nS.toNat = i + 2)
    (S3 : State) (hFr : Fr lo dst pS nS s S3)
    (hval : Janus.Spec.val256 S3.mem dst.toNat = v)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0xa4))
    (hx1 : S3.regs 1 = pS + BitVec.ofNat 64 (i + 1)) (hx2 : S3.regs 2 = nS - BitVec.ofNat 64 (i + 1))
    (hx4 : S3.regs 4 = BitVec.ofNat 64 (i + 1)) (hx5 : S3.regs 5 = pS) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xa4 = 754196 from by rw [h_sci]] at hpc3
  clear fsp
  have h28' : S3.regs 28 = s.regs 28 := f28
  have hpacc : S3.mem.accessible pS.toNat nS.toNat false = true := by
    rw [fmf.accessible]; rcases hPA with h | h
    · exact absurd h hn
    · exact h
  have hbyte : S3.mem.readLE (pS.toNat + (i + 1)) 1 = bytesAt s.mem pS.toNat (i + 1) :=
    fmf.readLE (pS.toNat + (i + 1)) 1 (str_outside hPW hPZ (by omega) hhi (i + 1) (by omega))
  have hbl : bytesAt s.mem pS.toNat (i + 1) < 256 := by
    have := Janus.Arm64.Memory.readLE_lt s.mem (pS.toNat + (i + 1)) 1
    show s.mem.readLE (pS.toNat + (i + 1)) 1 < 256
    simpa using this
  have hsp112 : S3.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : S3.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  have hadd : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := nS.isLt; omega
  clear hMod hEnv hMult hCh hPA hPW hPZ hzR hzS hzg
  by_cases hb : bytesAt s.mem pS.toNat (i + 1) = 48
  · have e3 : (addSub (BitVec.setWidth 32 (BitVec.ofNat 64 (bytesAt s.mem pS.toNat (i + 1)))) (48#32) true).snd.z = true := by
      rw [cmp_z32]; simp [hb]
    janus_run [hbyte, hpacc, hacc, hrfp, hrlr, hSal, h28', f28, ofn, e3] until [754228]
    refine post_ok cfg htop hlo112 hfr0 hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, h28']) (by simp [setReg_apply, f18])
      rfl (sci_e0 hn hsome hv (by omega) hb) (by simp [setReg_apply]) (by simp [setReg_apply]) hval
  · have e3 : (addSub (BitVec.setWidth 32 (BitVec.ofNat 64 (bytesAt s.mem pS.toNat (i + 1)))) (48#32) true).snd.z = false := by
      rw [cmp_z32]
      simp only [decide_eq_false_iff_not]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
      omega
    janus_run [hbyte, hpacc, hacc, hrfp, hrlr, hSal, h28', f28, ofn, e3] until [754228]
    refine found3 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn i hsome v hv (fun h => hb h.2) _
      (fr_of_eq hfr0 rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl) hval
      (by simp [h_sci]) ⟨fun h => absurd h (by omega), fun _ => by simp [setReg_apply, hx1]⟩ (by simp [setReg_apply, hx2])


theorem found2b (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v) (hc2 : nS.toNat = i + 2)
    (S3 : State) (hFr : Fr lo dst pS nS s S3)
    (hval : Janus.Spec.val256 S3.mem dst.toNat = v)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0x6c)) (hspill : S3.mem.readLE (S3.sp.toNat + 32) 8 = i) (hx0z : S3.regs 0 = 0)
 :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x6c = 754140 from by rw [h_sci]] at hpc3
  clear fsp
  have h28' : S3.regs 28 = s.regs 28 := f28
  have hpacc : True := trivial
  have hnS : nS = BitVec.ofNat 64 (i + 2) := BitVec.eq_of_toNat_eq (by
    simp only [BitVec.toNat_ofNat]; have := nS.isLt; omega)
  have e2 : (addSub (nS - BitVec.ofNat 64 i) 2#64 true).snd.z = true := by
    rw [cmp_z]; simp only [decide_eq_true_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := nS.isLt; omega
  have hmk : BitVec.ofNat 64 i + 1#64 &&& (0#64 - (nS - BitVec.ofNat 64 (i + 1))).sshiftRight 63 = BitVec.ofNat 64 i + 1#64 := by
    apply mask_pos
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nS.isLt; omega
  have hadd : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := nS.isLt; omega
  janus_run [hpc3, hx0z, hr136, hr128, hr120, hspill, hacc, hrfp, hrlr, h28', f28, hSal, e2, hmk] until [754196]
  case h =>
    exact found2b_ldrb impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn i hsome v hv hc2 _
      (fr_of_eq hfr0 rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl) hval
      (by simp [h_sci]) (by simp [setReg_apply, hadd]) (by simp [setReg_apply]) (by simp [setReg_apply, hadd]) (by simp [setReg_apply])

theorem found2 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v)
    (S3 : State) (hFr : Fr lo dst pS nS s S3) (hspill : S3.mem.readLE (S3.sp.toNat + 32) 8 = i)
    (hval : Janus.Spec.val256 S3.mem dst.toNat = v) (hx0z : S3.regs 0 = 0)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0x6c))  :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨hi_lt, -, -⟩ := idxE_some hsome
  by_cases hc1 : nS.toNat = i + 1
  · exact found2a impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre hn i hsome v hv S3 hFr hspill hval hx0z hpc3 hc1
  · by_cases hc2 : nS.toNat = i + 2
    · exact found2b impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre hn i hsome v hv hc2 S3 hFr hval hpc3 hspill hx0z
    · exact found2c impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre hn i hsome v hv S3 hFr hspill hval hx0z hpc3 (by omega)

theorem found1_after (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (Sx S3 : State) (hFrx : Fr lo dst pS nS s Sx) (hspill : Sx.mem.readLE (Sx.sp.toNat + 32) 8 = i)
    (hpc3 : S3.pc = BitVec.ofNat 64 (sciEntry + 0x6c))
    (hpost : TopPost cfg R R2 T b L lo (Sx.sp.toNat + 32) dst pS (BitVec.ofNat 64 i) Sx S3)
    (hreg3 : S3.mem.regions = Sx.mem.regions) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S3 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have htop' := htop
  obtain ⟨h30a, h30b, h0, h1, h2, hMod, hEnv, hlo, hhi, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS,
    hzg, hPA, hP48, hPW, hPZ, hCh⟩ := htop'
  have hEnv0 := hEnv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, -⟩ := hEnv0
  have hfr0 := hFrx
  obtain ⟨fsp, f28, f18, f29, fmf, freg, fra, ffp, fdst, fp, fn⟩ := hFrx
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  have hSsp : Sx.sp.toNat = s.sp.toNat - 112 := by
    rw [fsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrfp : Sx.mem.readLE (Sx.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [hSsp, show s.sp.toNat - 112 - 8 = s.sp.toNat - 120 by omega]; exact ffp
  have hrlr : Sx.mem.readLE Sx.sp.toNat 8 = (s.regs 30).toNat := by rw [hSsp]; exact fra
  have hacc : Sx.mem.accessible (Sx.sp.toNat - 8) 152 true = true := by
    rw [fmf.accessible]
    exact Janus.Arm64.Memory.accessible_sub _ hr5 (Or.inr rfl) (by omega) (by omega)
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x6c = 754140 from by rw [h_sci]] at hpc3
  have hSal : Sx.sp.toNat % 16 = 0 := by omega
  clear fsp
  have hsp112 : Sx.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : Sx.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  have hbS := bytes_xfer cfg htop hfr0
  have hi64 : (BitVec.ofNat 64 i).toNat = i := by simp [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  have hbytes : decParse (bytesAt s.mem pS.toNat) i = decParse (bytesAt Sx.mem pS.toNat) i :=
    Fv256.I.decParse_congr _ _ _ (fun k hk => (hbS k (by omega)).symm)
  have hpost' := hpost
  obtain ⟨k1, k2, k3, k4, k5, k6, hcases⟩ := hpost
  rw [hi64] at hcases
  have hra : S3.mem.readLE Sx.sp.toNat 8 = (s.regs 30).toNat := by rw [k6]; exact hrlr
  have hfp' : S3.mem.readLE (Sx.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [k5]; exact hrfp
  have hacc3 : S3.mem.accessible (Sx.sp.toNat - 8) 152 true = true := by
    have e : S3.mem.regions = Sx.mem.regions := hreg3
    unfold Janus.Arm64.Memory.accessible at hacc ⊢
    rw [e]; exact hacc
  have hacc3' : S3.mem.accessible (Sx.sp.toNat - 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (by omega) (by omega)
  have hr28' : S3.regs 28 = s.regs 28 := by rw [k3, f28]
  have hr18' : S3.regs 18 = s.regs 18 := by rw [k4, f18]
  have hhi' : Sx.sp.toNat + 32 ≤ s.sp.toNat - 8 := by omega
  have hbyt : decParse (bytesAt s.mem pS.toNat) i = decParse (bytesAt Sx.mem pS.toNat) i := hbytes
  have hdich := post_dichot cfg htop hlo112 hinit hitab_ne hfr0 (z' := dst) hhi' (Or.inl rfl) hpost'
  rw [hi64] at hdich
  rcases hdich with ⟨hx0z, v', hv', c1, cval, cMF⟩ | ⟨hx0z, hne0⟩
  · have hv'' : decParse (bytesAt s.mem pS.toNat) i = .ok v' := hbytes.trans hv'
    have hFr3 := fr_next cfg htop hlo112 hfr0 hhi' (Or.inl rfl) k1 k2 k3 k4 k5 k6 cMF hreg3
    have hspill3 : S3.mem.readLE (S3.sp.toNat + 32) 8 = i := by
      rw [k1]
      rw [cMF.readLE (Sx.sp.toNat + 32) 8 (by
        simp only [outside_cons, outside_nil, and_true]; have := top_zW cfg htop; omega)]
      exact hspill
    exact found2 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ hn i hsome v' hv'' S3 hFr3
      hspill3 cval hx0z hpc3
  · have hne : ∀ v, decParse (bytesAt s.mem pS.toNat) i ≠ .ok v := fun v h => hne0 v (hbytes.symm.trans h)
    janus_run [hra, hfp', hSal, ofn, hacc3, hacc3', hx0z]
    refine post_err cfg htop hlo112 hfr0 (by omega) (z' := dst) (Or.inl rfl) (off := 0) (pS' := pS) (nS' := BitVec.ofNat 64 i)
      (Or.inl ⟨by omega, by simp [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]; omega⟩) hpost'
      hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, hr28']) (by simp [setReg_apply, hr18']) (by simp [setReg_apply])
      (by simp [setReg_apply]) rfl (by rw [hi64]; exact hne)
      (fun h => by rw [hi64] at h; exact sci_mant_eof hn hsome h) (fun h => by rw [hi64] at h; exact sci_mant_range hn hsome h)
      (fun l n h => by rw [hi64] at h; simpa using sci_mant_syn hn hsome h)


theorem seg_found1 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0) (S : State) (hfr : Fr lo dst pS nS s S)
    (hpc : S.pc = BitVec.ofNat 64 (sciEntry + 0x44)) (h30 : S.regs 30 = BitVec.ofNat 64 (sciEntry + 0x44))
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (hx0 : (S.regs 0).toNat = i) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hfr
  obtain ⟨hl1, hl2, hl3, hl4, hP48, hl5⟩ := top_nums cfg htop
  have hfr0 := hfr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hfr
  obtain ⟨hi_lt, hi_e, hi_before⟩ := idxE_some hsome
  have hzW := top_zW cfg htop
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x44 = 754100 from by rw [h_sci]] at hpc h30
  clear fsp
  have h28' : S.regs 28 = s.regs 28 := f28
  have hi64 : (BitVec.ofNat 64 i).toNat = i := by simp [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  have hx : S.regs 0 = BitVec.ofNat 64 i := BitVec.eq_of_toNat_eq (by rw [hi64]; exact hx0)
  have e1 := e1_ne i (by omega)
  janus_run [e1, hpc, hx, hr136, hr128, hr120, hacc, hrfp, hrlr, h28', h30, f28, hSal] until [sfdEntry]
  case h =>
    have hF : MemFrame s.mem (S.mem.writeLE (BitVec.toNat S.sp + 32) 8 i) [(lo, hi), (dst.toNat, dst.toNat + 32)] := by
      janus_frame
    refine ReachesRet.call (Summary.regions (hsfd b L lo (S.sp.toNat + 32) dst pS (BitVec.ofNat 64 i))) (by first | rfl | decide) ?_ ?_
    · have a1 : S.sp.toNat + 32 ≤ hi := by omega
      have a4 : lo + 4528 ≤ S.sp.toNat := by omega
      refine call_pre cfg htop hF hSal a1 (Or.inl rfl) (by omega) (Or.inr ⟨Nat.le_refl _, by rw [hi64]; omega⟩) (by rw [hi64]; omega)
        (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
        (by simp [setReg_apply, f28]) a4 (by simp) (top_zR cfg htop) (top_zPr cfg htop) (top_zS cfg htop) (top_zg cfg htop)
        (by simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [fmf.accessible]; exact (top_zP cfg htop).1) (top_zP cfg htop).2
    · intro S3 hpc3 ⟨hpost, hreg3⟩
      have hF' : MemFrame S.mem (S.mem.writeLE (BitVec.toNat S.sp + 32) 8 i) [(S.sp.toNat + 32, S.sp.toNat + 104)] := by
        janus_frame
      refine found1_after impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn i hsome _ S3 ?_ ?_ (by rw [hpc3]; simp [setReg_apply, h_sci]) hpost hreg3
      · exact fr_loc hfr0 (by omega) (by omega) hF' (by simp) rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
      · show (S.mem.writeLE (S.sp.toNat + 32) 8 i).readLE (S.sp.toNat + 32) 8 = i
        rw [Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)

end Fv256.Arm64.ScanSci
