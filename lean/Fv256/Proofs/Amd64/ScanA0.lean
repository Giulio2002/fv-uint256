import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg

/-!
# `scanScientificFromString` (amd64), Level A segment: the empty string
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
/-- scanSci with an empty string: `Clear` and return nil -/
theorem sci_len0 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 sci)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat = 0) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret, hT, hlo, hav, hpg⟩ := hpre
  obtain ⟨h0, h3, h1, hMod, hEnv, hlo4, hhi, hMult, hEOF, hEOFo, hErr, hErro, hMax, hMaxo, hMaxR, hMaxV, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA⟩ := hT
  have hn0 : (s.regs 1).toNat = 0 := by rw [h1]; exact hn
  have hacc : s.mem.accessible (s.regs 0).toNat 32 true = true := by rw [h0]; exact hz
  have hz48 : (s.regs 0).toNat + 32 ≤ 2 ^ 48 := by rw [h0]; exact hzw
  janus64_run [hn0, hacc]
  have hx15 : s.xmm 15 = 0 := hret.2.2.1
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have e2 : (s.regs 4).toNat + 8 ≤ hi := hEnv.2.1
  have hx0 : (s.xmm 15).toNat = 0 := by rw [hx15]; rfl
  all_goals (
    refine ⟨?_, Or.inl ⟨0, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [Kept, retAddrOf, setRegF]
    · simp [sciParse, hn]
    · simp [setRegF]
    · simp [setRegF]
    · unfold Janus.Spec.val256
      rw [show (32:Nat) = 16 + 16 from rfl, Janus.Arm64.Memory.readLE_add]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, hx0]
    · refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (dst.toNat, dst.toNat + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (dst.toNat, dst.toNat + 32)) (by simp) (by omega) (by omega))

end Fv256.Amd64.ScanA
