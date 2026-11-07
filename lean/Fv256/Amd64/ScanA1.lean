import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanIbsCall
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
/-- `scanScientificFromString` (non-empty string): the prologue, the argument stores and the call of `IndexByteString.abi0` (`hibs`); ends at the
instruction after the call -/
theorem sci_ibs (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sci)
    (hibs : Fv256.IndexByte.IbsLibA (Extracted.program.link impl) ibsEntry avxAddr)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (sci + 0x53)) s
      (fun S => Fv256.Amd64.ScanIbsCall.PostK s S lo hi dst p n) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls⟩ := hpre
  obtain ⟨h0, h3, h1, hMod, hEnv, hlo4, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hT
  have hn0 : (s.regs 1).toNat ≠ 0 := by rw [h1]; exact hn
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have e2 : (s.regs 4).toNat + 8 ≤ hi := hEnv.2.1
  janus64_run [hn0] until [ibsEntry]
  refine ReachesRet.call (hibs p n 101) rfl ?_ (fun S' hr hq => ?_)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
    refine Fv256.Amd64.ScanIbsCall.pre_of_bv s.mem p n _ (sp := (s.regs 4).toNat) (v5 := (s.regs 5).toNat) (dst := dst.toNat)
      (ra := 4930611) (lo := lo) (hi := hi) rfl ?_ (by omega) (by omega) e4 (by omega) e3 e5 hav hpg hpw ?_
    · apply BitVec.eq_of_toNat_eq
      have := (s.regs 4).isLt
      simp only [setRegF_apply, BitVec.toNat_sub, BitVec.toNat_ofNat]
      simp
      omega
    · rcases hpW with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
    have hq' := hq
    refine ReachesRet.done ?_ ?_
    · rw [hr]
      simp only [retAddrOf, setRegF_apply]
      have hsp : (s.regs 4 - 120#64).toNat = (s.regs 4).toNat - 120 := by
        have := (s.regs 4).isLt
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [show (4 = 5) = False from by decide, if_false, if_true, hsp]
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      first | rfl | decide
    · refine Fv256.Amd64.ScanIbsCall.cont (lo := lo) (hi := hi) ?_ ?_ ?_ ?_ ?_ hq' hq'.2.2.2.2.1 hq'.2.2.2.2.2 e1 hhi hlo ?_
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · rfl
      · rfl
      · rfl
      · exact hpW

end Fv256.Amd64.ScanA
