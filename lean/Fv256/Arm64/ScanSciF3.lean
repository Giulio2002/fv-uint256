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

/-!
# `scanScientificFromString` (arm64): after the exponent parse: range check, `Exp`, `MulOverflow`
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

theorem found5_ret (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = Fv256.I.Res.range)
    (S6 : State) (hFr : Fr lo dst pS nS s S6) (hpc6 : S6.pc = BitVec.ofNat 64 (sciEntry + 0xf8)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S6 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  janus_eval_nat h_err : errBigAddr
  rw [show sciEntry + 0xf8 = 754280 from by rw [h_sci]] at hpc6
  clear fsp
  have h28' : S6.regs 28 = s.regs 28 := f28
  have hacc16 : S6.mem.accessible cfg.errBig 16 false = true := by
    rw [fmf.accessible]; exact (top_errBig cfg htop)
  have hsp112 : S6.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : S6.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  janus_run [hpc6, hacc, hrfp, hrlr, hSal, h28', f28, hacc16]
  exact post_range cfg htop hlo112 hfr0 hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, h28']) (by simp [setReg_apply, f18])
    rfl hsci (by simp only [setReg_apply]; simp [ofnat_rd8, cfg_errBig, h_err]) (by simp only [setReg_apply]; simp [ofnat_rd8, cfg_errBig, h_err])

theorem found7_ret (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = Fv256.I.Res.range)
    (S6 : State) (hFr : Fr lo dst pS nS s S6) (hpc6 : S6.pc = BitVec.ofNat 64 (sciEntry + 0x148)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S6 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  janus_eval_nat h_err : errBigAddr
  rw [show sciEntry + 0x148 = 754360 from by rw [h_sci]] at hpc6
  clear fsp
  have h28' : S6.regs 28 = s.regs 28 := f28
  have hacc16 : S6.mem.accessible cfg.errBig 16 false = true := by
    rw [fmf.accessible]; exact (top_errBig cfg htop)
  have hsp112 : S6.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : S6.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  janus_run [hpc6, hacc, hrfp, hrlr, hSal, h28', f28, hacc16]
  exact post_range cfg htop hlo112 hfr0 hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, h28']) (by simp [setReg_apply, f18])
    rfl hsci (by simp only [setReg_apply]; simp [ofnat_rd8, cfg_errBig, h_err]) (by simp only [setReg_apply]; simp [ofnat_rd8, cfg_errBig, h_err])

theorem found5a (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (e : Nat) (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = Fv256.I.Res.range)
    (S5 : State) (hFr : Fr lo dst pS nS s S5)
    (hexpv : Janus.Spec.val256 S5.mem (S5.sp.toNat + 72) = e) (hbig : 77 < e)
    (hpc5 : S5.pc = BitVec.ofNat 64 (sciEntry + 0xd8)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S5 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xd8 = 754248 from by rw [h_sci]] at hpc5
  clear fsp
  have h28' : S5.regs 28 = s.regs 28 := f28
  have hE : S5.mem.readLE (S5.sp.toNat + 72) 32 = e := hexpv
  rw [Fv256.Util.readLE_32] at hE
  simp only [Nat.add_assoc, Nat.reduceAdd] at hE
  have hacc2 : S5.mem.accessible (S5.sp.toNat + 72) 32 false = true := by
    exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  have l0 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 72) 8
  have l1 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 80) 8
  have l2 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 88) 8
  have l3 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 96) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  by_cases h0 : 77 < S5.mem.readLE (S5.sp.toNat + 72) 8
  · janus_run [hpc5, hacc, hrfp, hrlr, hSal, h28', f28, hacc2, h0] until [754280]
    exact found5_ret impl R R2 T b L lo hi dst pS nS s hpre0 hsci _ (fr_of_eq hfr0 rfl rfl rfl rfl rfl) (by simp [h_sci])
  · have hcz : BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 96) 8) |||
        (BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 80) 8) ||| BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 88) 8)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_or, BitVec.toNat_ofNat] at h'
      simp only [Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2, Nat.mod_eq_of_lt l3] at h'
      simp at h'
      omega
    have hcz' : ¬ (S5.mem.readLE (S5.sp.toNat + 96) 8 ||| (S5.mem.readLE (S5.sp.toNat + 80) 8 ||| S5.mem.readLE (S5.sp.toNat + 88) 8) = 0) := by
      intro h
      rw [Nat.or_eq_zero_iff, Nat.or_eq_zero_iff] at h
      omega
    janus_run [hpc5, hacc, hrfp, hrlr, hSal, h28', f28, hacc2, h0, hcz, hcz'] until [754280]
    exact found5_ret impl R R2 T b L lo hi dst pS nS s hpre0 hsci _ (fr_of_eq hfr0 rfl rfl rfl rfl rfl) (by simp [h_sci])

theorem found7 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (v e : Nat) (hv : v < 2 ^ 256) (hsmall : e ≤ 77)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S7 : State) (hFr : Fr lo dst pS nS s S7)
    (hflag : (S7.regs 1).toNat = (if Spec.W ≤ v * 10 ^ e then 1 else 0))
    (hval : Janus.Spec.val256 S7.mem dst.toNat = Spec.mul v (10 ^ e))
    (hpc7 : S7.pc = BitVec.ofNat 64 (sciEntry + 0x144)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S7 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x144 = 754356 from by rw [h_sci]] at hpc7
  clear fsp
  have h28' : S7.regs 28 = s.regs 28 := f28
  have hsp112 : S7.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : S7.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  have hW : Spec.W = 2 ^ 256 := rfl
  by_cases hov : 2 ^ 256 ≤ v * 10 ^ e
  · have hx1 : S7.regs 1 = 1#64 := BitVec.eq_of_toNat_eq (by rw [hflag, hW]; simp [hov])
    rw [if_pos hov] at hsci
    janus_run [hpc7, hacc, hrfp, hrlr, hSal, h28', f28, hx1] until [754360]
    exact found7_ret impl R R2 T b L lo hi dst pS nS s hpre0 hsci _ (fr_of_eq hfr0 rfl rfl rfl rfl rfl) (by simp [h_sci])
  · have hx1 : S7.regs 1 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hflag, hW]; simp [hov])
    rw [if_neg hov] at hsci
    janus_run [hpc7, hacc, hrfp, hrlr, hSal, h28', f28, hx1]
    refine post_ok cfg htop hlo112 hfr0 hsp112 (by simp [setReg_apply]) (by simp [setReg_apply, h28']) (by simp [setReg_apply, f18])
      rfl hsci (by simp [setReg_apply]) (by simp [setReg_apply]) ?_
    rw [hval]
    unfold Spec.mul
    exact Nat.mod_eq_of_lt (by simpa [hW] using hov)

theorem found6_after (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (v e : Nat) (hv : v < 2 ^ 256) (hsmall : e ≤ 77)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S6 Sc S7 : State) (hpost : MoPostS dst dst (S6.sp + 72#64) Sc S7) (hFr : Fr lo dst pS nS s S6) (hval : Janus.Spec.val256 S6.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S6.mem (S6.sp.toNat + 72) = 10 ^ e)
    (hscsp : Sc.sp = S6.sp) (hscm : Sc.mem = S6.mem) (hsc28 : Sc.regs 28 = S6.regs 28) (hsc29 : Sc.regs 29 = S6.regs 29)
    (hsc18 : Sc.regs 18 = S6.regs 18)
    (hpc7 : S7.pc = Sc.regs GoABI.regLR) (hsc30 : Sc.regs GoABI.regLR = 754356#64) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S7 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have hfr0 := hFr
  obtain ⟨hSsp, -⟩ := frame_facts cfg htop hlo112 hFr
  janus_eval_nat h_sci : sciEntry
  have hz72 : (S6.sp + 72#64).toNat = S6.sp.toNat + 72 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := S6.sp.isLt; omega)
  have hk := hpost.1
  have cflag := hpost.2.2.1
  have cval := hpost.2.2.2.1
  have cow := hpost.2.2.2.2
  rw [hz72, hscm] at cflag cval
  rw [hscm, hscsp] at cow
  have hzW := top_zW cfg htop
  have hl1 := (top_nums cfg htop).2.1
  have k1 := hk.1
  have k2 := hk.2.1
  have k3 := hk.2.2.1
  have k4 := hk.2.2.2
  rw [hscsp] at k1
  refine found7 impl R R2 T b L lo hi dst pS nS s hpre0 v e hv hsmall hsci S7
    (fr_of_ow3 hfr0 (by omega) (by omega) (by omega) cow k1 (by rw [k2, hsc28]) (by rw [k4, hsc18]) (by rw [k3, hsc29])) ?_ ?_ (by rw [hpc7, hsc30]; simp [h_sci])
  · rw [cflag, hval, hexpv]
  · rw [cval, hval, hexpv]

theorem found6 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (v e : Nat) (hv : v < 2 ^ 256) (hsmall : e ≤ 77)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S6 : State) (hFr : Fr lo dst pS nS s S6) (hval : Janus.Spec.val256 S6.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S6.mem (S6.sp.toNat + 72) = 10 ^ e)
    (hpc6 : S6.pc = BitVec.ofNat 64 (sciEntry + 0x134)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S6 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0x134 = 754340 from by rw [h_sci]] at hpc6
  clear fsp
  have h28' : S6.regs 28 = s.regs 28 := f28
  have hacc2 : S6.mem.accessible (S6.sp.toNat + 72) 32 false = true := by
    exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  janus_run [hpc6, hacc, hrfp, hrlr, hSal, h28', f28, hr120, hacc2] until [moEntry]
  case h =>
    refine ReachesRet.call (hmo dst dst (S6.sp + 72#64)) (by first | rfl | decide) ?_ ?_
    · have hRA : RetAddr Fv256.Arm64.MulOverflowProg.program 754356 := ⟨by decide, by decide, by decide, by decide⟩
      refine ⟨hRA, ?_, mo_call_pre cfg htop hlo112 hfr0 rfl rfl rfl⟩
      simp [ArgsFrom, setReg_apply]
    · intro S7 hpc7 hpost
      exact found6_after impl R R2 T b L lo hi dst pS nS s hpre0 v e hv hsmall hsci S6 _ S7 hpost hfr0 hval hexpv rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) hpc7 rfl

theorem found5b_after (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s)
    (v e : Nat) (hv : v < 2 ^ 256) (hsmall : e ≤ 77)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S5 Sc S6 : State) (hpost : ExpPost Sc S6) (hFr : Fr lo dst pS nS s S5) (hval : Janus.Spec.val256 S5.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S5.mem (S5.sp.toNat + 72) = e)
    (hscsp : Sc.sp = S5.sp) (hsc28 : Sc.regs 28 = S5.regs 28) (hsc29 : Sc.regs 29 = S5.regs 29) (hsc18 : Sc.regs 18 = S5.regs 18)
    (hsc0 : Sc.regs 0 = S5.sp + 72#64) (hsc1 : Sc.regs 1 = S5.sp + 40#64) (hsc2 : Sc.regs 2 = S5.sp + 72#64)
    (hsc30 : Sc.regs 30 = 754340#64) (hregc : S6.mem.regions = Sc.mem.regions)
    (hscm : Sc.mem = ((((S5.mem.writeLE (S5.sp.toNat + 40) 8 0).writeLE (S5.sp.toNat + 48) 8 0).writeLE (S5.sp.toNat + 56) 8 0).writeLE
      (S5.sp.toNat + 64) 8 0).writeLE (S5.sp.toNat + 40) 8 10) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S6 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have hfr0 := hFr
  obtain ⟨hSsp, -⟩ := frame_facts cfg htop hlo112 hFr
  janus_eval_nat h_sci : sciEntry
  have hz72 : (S5.sp + 72#64).toNat = S5.sp.toNat + 72 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := S5.sp.isLt; omega)
  have hz40 : (S5.sp + 40#64).toNat = S5.sp.toNat + 40 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := S5.sp.isLt; omega)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpost
  have hzW := top_zW cfg htop
  have hl1 := (top_nums cfg htop).2.1
  have hF1 : MemFrame S5.mem Sc.mem [(S5.sp.toNat + 40, S5.sp.toNat + 72)] := by
    rw [hscm]; janus_frame
  have hFrc : Fr lo dst pS nS s Sc :=
    fr_gen hfr0 hF1 (by rw [hscm]; simp) (fun a n ho => by simp only [outside_cons, outside_nil, and_true] at ho ⊢; omega)
      (fun a ha => by simp only [outside_cons, outside_nil, and_true]; omega) hscsp hsc28 hsc18 hsc29
  have hscn : Sc.sp.toNat = S5.sp.toNat := by rw [hscsp]
  rw [hsc0, hz72] at p9
  rw [hscn] at p9
  have hFr6 : Fr lo dst pS nS s S6 := by
    refine fr_gen hFrc p9 hregc ?_ ?_ (by rw [p2, hscsp]) (by rw [p5, hsc28]) (by rw [p4, hsc18]) (by rw [p6, hsc29])
    · intro a n ho
      simp only [outside_cons, outside_nil, and_true] at ho ⊢
      omega
    · intro a ha
      simp only [outside_cons, outside_nil, and_true]
      omega
  have hvalc : Janus.Spec.val256 Sc.mem dst.toNat = v := by
    unfold Janus.Spec.val256
    rw [hF1.readLE dst.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hval
  have hval6 : Janus.Spec.val256 S6.mem dst.toNat = v := by
    unfold Janus.Spec.val256
    rw [p9.readLE dst.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hvalc
  have hbase : Sc.mem.readLE (S5.sp.toNat + 40) 32 = 10 := by
    rw [hscm, Fv256.Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  have hexpc : Sc.mem.readLE (S5.sp.toNat + 72) 32 = e := by
    rw [hF1.readLE (S5.sp.toNat + 72) 32 (by simp only [outside_cons, outside_nil, and_true]; omega)]
    exact hexpv
  have hexp6 : Janus.Spec.val256 S6.mem (S6.sp.toNat + 72) = 10 ^ e := by
    unfold Janus.Spec.val256
    rw [p2, hscsp]
    rw [hsc0, hz72, hsc1, hz40, hsc2, hz72, hbase, hexpc] at p8
    rw [p8]
    unfold Fv256.F.expSpec
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hsmall) (by decide))
  refine found6 impl R R2 T b L lo hi dst pS nS hmo s hpre0 v e hv hsmall hsci S6 hFr6 hval6 hexp6 ?_
  rw [p1, hsc30]; simp [h_sci]

theorem found5b (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (v e : Nat) (hv : v < 2 ^ 256)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S5 : State) (hFr : Fr lo dst pS nS s S5) (hval : Janus.Spec.val256 S5.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S5.mem (S5.sp.toNat + 72) = e) (hsmall : e ≤ 77)
    (hpc5 : S5.pc = BitVec.ofNat 64 (sciEntry + 0xd8)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S5 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xd8 = 754248 from by rw [h_sci]] at hpc5
  clear fsp
  have h28' : S5.regs 28 = s.regs 28 := f28
  have hE : S5.mem.readLE (S5.sp.toNat + 72) 32 = e := hexpv
  rw [Fv256.Util.readLE_32] at hE
  simp only [Nat.add_assoc, Nat.reduceAdd] at hE
  have hacc2 : S5.mem.accessible (S5.sp.toNat + 72) 32 false = true := by
    exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inl rfl) (by omega) (by omega)
  have l0 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 72) 8
  have l1 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 80) 8
  have l2 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 88) 8
  have l3 := Janus.Arm64.Memory.readLE_lt S5.mem (S5.sp.toNat + 96) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  have hn0 : ¬ 77 < S5.mem.readLE (S5.sp.toNat + 72) 8 := by omega
  have hcz' : S5.mem.readLE (S5.sp.toNat + 96) 8 ||| (S5.mem.readLE (S5.sp.toNat + 80) 8 ||| S5.mem.readLE (S5.sp.toNat + 88) 8) = 0 := by
    rw [Nat.or_eq_zero_iff, Nat.or_eq_zero_iff]
    omega
  have hcz : BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 96) 8) |||
      (BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 80) 8) ||| BitVec.ofNat 64 (S5.mem.readLE (S5.sp.toNat + 88) 8)) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2, Nat.mod_eq_of_lt l3]
    rw [hcz']; rfl
  have hacc3 : S5.mem.accessible (S5.sp.toNat + 40) 64 true = true := by
    rw [fmf.accessible]
    obtain ⟨hn1, hn2, hn3, hn4, hn5, hl5⟩ := top_nums cfg htop
    exact Janus.Arm64.Memory.accessible_sub _ hl5 (Or.inr rfl) (by omega) (by omega)
  janus_run [hpc5, hacc, hrfp, hrlr, hSal, h28', f28, hacc2, hn0, hcz, hcz', hacc3] until [expEntry]
  case h =>
    have hF1 : MemFrame S5.mem ((((S5.mem.writeLE (S5.sp.toNat + 40) 8 0).writeLE (S5.sp.toNat + 48) 8 0).writeLE (S5.sp.toNat + 56) 8 0).writeLE
      (S5.sp.toNat + 64) 8 0 |>.writeLE (S5.sp.toNat + 40) 8 10) [(S5.sp.toNat + 40, S5.sp.toNat + 72)] := by
      janus_frame
    refine ReachesRet.call (Summary.regions hexp) (by first | rfl | decide) ?_ ?_
    · refine exp_call_pre cfg htop hlo112 hfr0 ?_ rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply]) (hF1.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; omega))
      refine dl_frame (dl_of_fr cfg htop hfr0 hdl) hF1 (by simp) (fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inr rfl) (Nat.le_refl _) (by simp)
    · intro S6 hpc6 ⟨hpost, hreg6⟩
      exact found5b_after impl R R2 T b L lo hi dst pS nS hmo s hpre0 v e hv hsmall hsci S5 _ S6 hpost hfr0 hval hexpv rfl rfl rfl rfl
        (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) hreg6 rfl

theorem found5 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (v e : Nat)
    (hsci : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
      (if 77 < e ∨ 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)))
    (S5 : State) (hFr : Fr lo dst pS nS s S5) (hval : Janus.Spec.val256 S5.mem dst.toNat = v)
    (hexpv : Janus.Spec.val256 S5.mem (S5.sp.toNat + 72) = e) (hx0z : S5.regs 0 = 0)
    (hpc5 : S5.pc = BitVec.ofNat 64 (sciEntry + 0xd4)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S5 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  have hfr0 := hFr
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xd4 = 754244 from by rw [h_sci]] at hpc5
  have hvlt : v < 2 ^ 256 := by
    rw [← hval]
    have := Janus.Arm64.Memory.readLE_lt S5.mem dst.toNat 32
    simpa [Janus.Spec.val256] using this
  by_cases hbig : 77 < e
  · have hsc : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat = Fv256.I.Res.range := by
      rw [hsci]; simp [hbig]
    janus_run [hpc5, hx0z] until [754248]
    exact found5a impl R R2 T b L lo hi dst pS nS s hpre0 e hsc _ (fr_of_eq hfr0 rfl rfl rfl rfl rfl) hexpv hbig (by simp [h_sci])
  · have hsmall : e ≤ 77 := by omega
    have hsc : Fv256.ScanSpec.sciParse (bytesAt s.mem pS.toNat) nS.toNat =
        (if 2 ^ 256 ≤ v * 10 ^ e then Fv256.I.Res.range else Fv256.I.Res.ok (v * 10 ^ e)) := by
      rw [hsci]; simp [hbig]
    janus_run [hpc5, hx0z] until [754248]
    exact found5b impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn v e hvlt hsc _ (fr_of_eq hfr0 rfl rfl rfl rfl rfl) hval hexpv hsmall
      (by simp [h_sci])

end Fv256.Arm64.ScanSci
