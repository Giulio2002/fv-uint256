import Extracted
import Fv256.Proofs.Arm64.ScanSpec
import Fv256.Proofs.Arm64.ScanCall
import Fv256.Proofs.Arm64.ScanSciBase

/-!
# `Scan` (arm64), the `nil` case: `Scan(nil)` clears the receiver and returns nil
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSpec

namespace Fv256.Arm64.ScanNil

abbrev scanEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Scan"

theorem scan_nil (impl : List Janus.Segment) (lo hi : Nat) (dst : BitVec 64) (s : State)
    (hpc : s.pc = BitVec.ofNat 64 scanEntry)
    (h0 : s.regs 0 = dst) (h1 : s.regs 1 = 0) (hlo : lo + 4720 ≤ s.sp.toNat) (hhi : s.sp.toNat + 32 ≤ hi)
    (h48 : hi ≤ 2 ^ 48) (hg : GuardOK s 80) (hsal : s.sp.toNat % 16 = 0) (hd : Ptr s.mem dst 32 true)
    (hw : dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat) (hacc : s.mem.accessible lo (hi - lo) true = true)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48) :
    ReachesRet (Extracted.program.link impl) (s.regs GoABI.regLR) s
      (fun s' => s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = 0 ∧
        MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] ∧ Kept s s') := by
  janus_eval_nat h_sc : scanEntry
  rw [h_sc] at hpc
  have hacc2 : s.mem.accessible (s.sp.toNat - 88) 120 true = true :=
    Janus.Arm64.Memory.accessible_sub _ hacc (Or.inr rfl) (by omega) (by omega)
  have h30b' : (s.regs 30).toNat < 2 ^ 56 := by omega
  have hd' : s.mem.accessible dst.toNat 32 true = true := hd.1
  have hd48 : dst.toNat + 32 ≤ 2 ^ 48 := hd.2
  janus_run [hpc, h0, h1, hg, hacc2, hsal, hd', h30b', h30a]
  refine ⟨by janus_frame, ?_⟩
  simp [Kept, setReg_apply]

end Fv256.Arm64.ScanNil
