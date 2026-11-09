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
import Fv256.Proofs.Arm64.ScanSciF3

/-!
# `scanScientificFromString` (arm64): the exponent: second `SetFromDecimal` call (on `s[idx+1:]`, destination the local `exp`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec

namespace Fv256.Arm64.ScanSci

theorem found4 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v)
    (hnot0 : ¬ (nS.toNat - (i + 1) = 1 ∧ bytesAt s.mem pS.toNat (i + 1) = 48))
    (pS' nS' : BitVec 64) (hn' : nS'.toNat = nS.toNat - (i + 1)) (hp' : nS'.toNat = 0 ∨ pS'.toNat = pS.toNat + (i + 1))
    (hsubs : nS'.toNat = 0 ∨ (pS.toNat ≤ pS'.toNat ∧ pS'.toNat + nS'.toNat ≤ pS.toNat + nS.toNat))
    (Sx S5 : State) (hFrx : Fr lo dst pS nS s Sx) (hval : Janus.Spec.val256 Sx.mem dst.toNat = v)
    (hpc5 : S5.pc = BitVec.ofNat 64 (sciEntry + 0xd4))
    (hpost : TopPost cfg R R2 T b L lo (Sx.sp.toNat + 72) (Sx.sp + 72#64) pS' nS' Sx S5)
    (hreg5 : S5.mem.regions = Sx.mem.regions) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S5 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  have hpre0 := hpre
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFrx
  obtain ⟨hl1, hl2, hl3, hl4, hP48, hl5⟩ := top_nums cfg htop
  have h30a : (s.regs 30).toNat % 4 = 0 := htop.1
  have h30b : (s.regs 30).toNat < 2 ^ 48 := htop.2.1
  obtain ⟨hi_lt, -, -⟩ := idxE_some hsome
  have hfr0 := hFrx
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFrx
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xd4 = 754244 from by rw [h_sci]] at hpc5
  clear fsp
  have hz'n : (Sx.sp + 72#64).toNat = Sx.sp.toNat + 72 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := Sx.sp.isLt; omega)
  have hhi' : Sx.sp.toNat + 72 ≤ s.sp.toNat - 8 := by omega
  have hz' : (Sx.sp + 72#64).toNat = dst.toNat ∨ (lo ≤ (Sx.sp + 72#64).toNat ∧ (Sx.sp + 72#64).toNat + 32 ≤ s.sp.toNat - 8) :=
    Or.inr ⟨by omega, by omega⟩
  have hpost' := hpost
  obtain ⟨k1, k2, k3, k4, k5, k6, -⟩ := hpost'
  have hra : S5.mem.readLE Sx.sp.toNat 8 = (s.regs 30).toNat := by rw [k6]; exact hrlr
  have hfp' : S5.mem.readLE (Sx.sp.toNat - 8) 8 = (s.regs 29).toNat := by rw [k5]; exact hrfp
  have hacc3 : S5.mem.accessible (Sx.sp.toNat - 8) 152 true = true := by
    unfold Janus.Arm64.Memory.accessible at hacc ⊢
    rw [hreg5]; exact hacc
  have hacc3' : S5.mem.accessible (Sx.sp.toNat - 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc3 (Or.inl rfl) (by omega) (by omega)
  have hr28' : S5.regs 28 = s.regs 28 := by rw [k3, f28]
  have hr18' : S5.regs 18 = s.regs 18 := by rw [k4, f18]
  have hsp112 : Sx.sp + 112#64 = s.sp := BitVec.eq_of_toNat_eq (by
    have hsi : Sx.sp.toNat + 112 = s.sp.toNat := by omega
    rw [BitVec.toNat_add, show (112#64).toNat = 112 from rfl, hsi]; exact Nat.mod_eq_of_lt s.sp.isLt)
  have hbS := bytes_xfer cfg htop hfr0
  have hbyt : decParse (bytesAt s.mem pS'.toNat) nS'.toNat = decParse (bytesAt Sx.mem pS'.toNat) nS'.toNat :=
    Fv256.I.decParse_congr _ _ _ (fun k hk => by
      rcases hp' with h | h
      · omega
      · have := hbS (i + 1 + k) (by omega)
        show s.mem.readLE (pS'.toNat + k) 1 = Sx.mem.readLE (pS'.toNat + k) 1
        rw [h, show pS.toNat + (i + 1) + k = pS.toNat + (i + 1 + k) by omega]; exact this.symm)
  have hexb := exp_bytes_eq (m := s.mem) (pS := pS) (nS := nS.toNat) hn' hp'
  have hdich := post_dichot cfg htop hlo112 hinit hitab_ne hfr0 hhi' hz' hpost
  rcases hdich with ⟨hx0z, e, he, c1, cval, cMF⟩ | ⟨hx0z, hne⟩
  · have he' : decParse (fun k => bytesAt s.mem pS.toNat (i + 1 + k)) (nS.toNat - (i + 1)) = .ok e := by
      rw [← hexb, hbyt]; exact he
    have hsci := sci_exp_ok hn hsome hv hnot0 he'
    have hFr5 := fr_next cfg htop hlo112 hfr0 hhi' hz' k1 k2 k3 k4 k5 k6 cMF hreg5
    have hdstS : Outside dst.toNat 32 [(lo, Sx.sp.toNat + 72), ((Sx.sp + 72#64).toNat, (Sx.sp + 72#64).toNat + 32)] :=
      dst_out2 (top_zW cfg htop) (by omega) (by omega) (by omega)
    refine found5 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s hpre0 hn v e hsci S5 hFr5 ?_ ?_ hx0z hpc5
    · show S5.mem.readLE dst.toNat 32 = v
      rw [cMF.readLE _ _ hdstS]; exact hval
    · show S5.mem.readLE (S5.sp.toNat + 72) 32 = e
      rw [k1, ← hz'n]; exact cval
  · have hne' : ∀ v, decParse (bytesAt s.mem pS'.toNat) nS'.toNat ≠ .ok v := fun v h => hne v (hbyt.symm.trans h)
    janus_run [hra, hfp', hSal, ofn, hacc3, hacc3', hx0z]
    refine post_err cfg htop hlo112 hfr0 hhi' hz' (off := i + 1) (by rcases hp' with h | h; exact Or.inr h; exact Or.inl ⟨h, by omega⟩) hpost hsp112 (by simp [setReg_apply])
      (by simp [setReg_apply, hr28']) (by simp [setReg_apply, hr18']) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl hne'
      (fun h => sci_exp_eof hn hsome hv hnot0 (by rw [← hexb]; exact h))
      (fun h => sci_exp_range hn hsome hv hnot0 (by rw [← hexb]; exact h))
      (fun l n h => sci_exp_syn hn hsome hv hnot0 (by rw [← hexb]; exact h))

theorem found3 (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst pS nS : BitVec 64) (hsfd : HSfd impl R R2 T) (hexp : HExp impl) (hmo : HMo impl)
    (s : State) (hpre : Pre0 R R2 T b L lo hi dst pS nS s) (hn : nS.toNat ≠ 0)
    (i : Nat) (hsome : Fv256.ScanSpec.idxE (bytesAt s.mem pS.toNat) nS.toNat = some i)
    (v : Nat) (hv : decParse (bytesAt s.mem pS.toNat) i = .ok v)
    (hnot0 : ¬ (nS.toNat - (i + 1) = 1 ∧ bytesAt s.mem pS.toNat (i + 1) = 48))
    (S4 : State) (hFr : Fr lo dst pS nS s S4) (hval : Janus.Spec.val256 S4.mem dst.toNat = v)
    (hpc4 : S4.pc = BitVec.ofNat 64 (sciEntry + 0xc4))
    (hx1 : (nS.toNat = i + 1 → S4.regs 1 = pS) ∧ (i + 1 < nS.toNat → S4.regs 1 = pS + BitVec.ofNat 64 (i + 1)))
    (hx2 : S4.regs 2 = nS - BitVec.ofNat 64 (i + 1)) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) S4 (SciPost cfg R R2 T b L lo hi dst pS nS s) := by
  obtain ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ := hpre
  obtain ⟨hSsp, hSal, hr136, hr128, hr120, hrfp, hrlr, hacc⟩ := frame_facts cfg htop hlo112 hFr
  obtain ⟨hl1, hl2, hl3, hl4, hP48, hl5⟩ := top_nums cfg htop
  obtain ⟨hn2, hsubs, hP48s, hp'⟩ := exp_args (i := i) (by obtain ⟨a, b, c⟩ := idxE_some hsome; exact a) hP48 hx1 hx2
  have hfr0 := hFr
  obtain ⟨fsp, f28, f18, f29, fmf, -⟩ := hFr
  janus_eval_nat h_sci : sciEntry
  rw [show sciEntry + 0xc4 = 754228 from by rw [h_sci]] at hpc4
  clear fsp
  have h28' : S4.regs 28 = s.regs 28 := f28
  have hacc2 : S4.mem.accessible (S4.sp.toNat + 72) 32 true = true := by
    exact Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega)
  have hz'n : (S4.sp + 72#64).toNat = S4.sp.toNat + 72 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := S4.sp.isLt; omega)
  janus_run [hpc4, hx2, hacc, hacc2, hrfp, hrlr, h28', f28, hSal] until [sfdEntry]
  case h =>
    have hF : MemFrame s.mem (((S4.mem.writeLE (BitVec.toNat S4.sp + 72) 8 0).writeLE (BitVec.toNat S4.sp + 80) 8 0).writeLE
              (BitVec.toNat S4.sp + 88) 8 0 |>.writeLE (BitVec.toNat S4.sp + 96) 8 0) [(lo, hi), (dst.toNat, dst.toNat + 32)] := by
      janus_frame
    refine ReachesRet.call (Summary.regions (hsfd b L lo (S4.sp.toNat + 72) (S4.sp + 72#64) (S4.regs 1) (S4.regs 2))) (by first | rfl | decide) ?_ ?_
    · have a1 : S4.sp.toNat + 72 ≤ hi := by omega
      have a2 : lo ≤ S4.sp.toNat + 72 := by omega
      have a3 : S4.sp.toNat + 72 + 32 ≤ hi := by omega
      have a4 : lo + 4528 ≤ S4.sp.toNat := by omega
      have a5 : S4.sp.toNat + 32 ≤ S4.sp.toNat + 72 := by omega
      have a6 : S4.sp.toNat + 72 + 32 ≤ 2 ^ 48 := by omega
      have hloc := local_facts cfg htop (z' := S4.sp.toNat + 72) a2 a3
      refine call_pre cfg htop hF hSal a1 (Or.inr ⟨by rw [hz'n]; exact a2, by rw [hz'n]; exact a3⟩) (Or.inr (Nat.le_of_eq hz'n.symm))
        hsubs hP48s (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply, f28]) a4 a5 (by rw [hz'n]; exact hloc.1)
        (by rw [hz'n]; exact hloc.2.1) (by rw [hz'n]; exact hloc.2.2.1) (by rw [hz'n]; exact hloc.2.2.2) ?_ (by rw [hz'n]; exact a6)
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      rw [hz'n]; exact hacc2
    · intro S5 hpc5 ⟨hpost, hreg5⟩
      refine found4 impl R R2 T b L lo hi dst pS nS hsfd hexp hmo s ⟨⟨htop, hlo112, hpage⟩, hinit, hdl⟩ hn i hsome v hv hnot0
        (S4.regs 1) (S4.regs 2) hn2 hp' hsubs _ S5 ?_ ?_ (by rw [hpc5]; simp [setReg_apply, h_sci]) hpost hreg5
      · have hF' : MemFrame S4.mem ((((S4.mem.writeLE (BitVec.toNat S4.sp + 72) 8 0).writeLE (BitVec.toNat S4.sp + 80) 8 0).writeLE
              (BitVec.toNat S4.sp + 88) 8 0).writeLE (BitVec.toNat S4.sp + 96) 8 0) [(S4.sp.toNat + 32, S4.sp.toNat + 104)] := by
          janus_frame
        exact fr_loc hfr0 (by omega) (by omega) hF' (by simp) rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
      · have hF' : MemFrame S4.mem ((((S4.mem.writeLE (BitVec.toNat S4.sp + 72) 8 0).writeLE (BitVec.toNat S4.sp + 80) 8 0).writeLE
              (BitVec.toNat S4.sp + 88) 8 0).writeLE (BitVec.toNat S4.sp + 96) 8 0) [(S4.sp.toNat + 32, S4.sp.toNat + 104)] := by
          janus_frame
        have hzW := top_zW cfg htop
        unfold Janus.Spec.val256
        dsimp only
        rw [hF'.readLE dst.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)]
        exact hval

end Fv256.Arm64.ScanSci
