import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg

/-!
# `Scan` (amd64), Level B segment: the nil source
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanB

set_option maxRecDepth 100000 in
/-- Scan with a nil source: `Clear` and return nil -/
theorem scan_nil (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s) (htw : tw = 0) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  subst htw
  obtain ⟨h0, h3, h1, hlo, hhi, hcase⟩ := hpre
  rcases hcase with ⟨-, ⟨hzw, hz⟩, hzW, hwin, hh48, hg1, hg2, hg3⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have hn0 : (s.regs 3).toNat = 0 := by rw [h3]; rfl
    have hacc : s.mem.accessible (s.regs 0).toNat 32 true = true := by rw [h0]; exact hz
    have hz48 : (s.regs 0).toNat + 32 ≤ 2 ^ 48 := by rw [h0]; exact hzw
    have hsp := (s.regs 4).isLt
    have hx15 : s.xmm 15 = 0 := hret.2.2.1
    have hx0 : (s.xmm 15).toNat = 0 := by rw [hx15]; rfl
    have hw1 : s.mem.accessible ((s.regs 4).toNat - 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem hwin (Or.inr rfl) (by omega) (by omega)
    have hw2 : s.mem.accessible ((s.regs 4).toNat + 16) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem hwin (Or.inr rfl) (by omega) (by omega)
    have hw3 : s.mem.accessible ((s.regs 4).toNat + 24) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem hwin (Or.inr rfl) (by omega) (by omega)
    have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
    janus64_run [hn0, hacc, hg1, hg2, hg3]
    all_goals (
      have e1 : lo ≤ (s.regs 4).toNat := by omega
      refine ⟨?_, Or.inl ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
      · simp [Kept, retAddrOf, setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · unfold Janus.Spec.val256
        rw [show (32:Nat) = 16 + 16 from rfl, Janus.Arm64.Memory.readLE_add]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, hx0]
      · refine ((((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (dst.toNat, dst.toNat + 32)) (by simp) (by omega) (by omega)).writeLE _ (r := (dst.toNat, dst.toNat + 32)) (by simp) (by omega) (by omega))
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd rfl h

end Fv256.Amd64.ScanB
