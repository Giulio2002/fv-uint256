import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.DecMath
import Fv256.Arm64.DecT
import Fv256.Arm64.DecA
import Fv256.Arm64.DecJ
import Fv256.Arm64.DecK

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- Summary of `internal/strconv.formatBase10(a []byte, u uint64) int` (arm64): `a[len-decLen u:]` holds the decimal digits of `u`. -/
theorem fb10_summary :
    Summary Extracted.program fb
      (fun s => GuardOK s 0 ∧ s.sp.toNat % 16 = 0 ∧ 24 ≤ s.sp.toNat ∧ s.sp.toNat + 16 + 8 < 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 24) 40 true = true ∧
        (s.regs 0).toNat + (s.regs 1).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true ∧
        decLen (s.regs 3).toNat ≤ (s.regs 1).toNat ∧
        ((s.regs 0).toNat + (s.regs 1).toNat ≤ s.sp.toNat - 24 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        TabsOK s.mem ∧ (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 ((s.regs 1).toNat - decLen (s.regs 3).toNat) ∧ s'.sp = s.sp ∧
        s'.regs 29 = s.regs 29 ∧ (∀ k, k ∉ Clob → s'.regs k = s.regs k) ∧
        (∀ k, k < decLen (s.regs 3).toNat →
          s'.mem.readLE ((s.regs 0).toNat + (s.regs 1).toNat - 1 - k) 1 = 48 + (s.regs 3).toNat / 10 ^ k % 10) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat + (s.regs 1).toNat - decLen (s.regs 3).toNat, (s.regs 0).toNat + (s.regs 1).toNat),
          (s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)] ∧ TabsOK s'.mem) := by
  intro s hpc ⟨hg, hal, h24, hsp2, hw, hp, hacc, hdl, hout, hd, hret, hret4⟩
  have hu64 := (s.regs 3).isLt
  have hs := s.sp.isLt
  have hr29 := (s.regs 29).isLt
  rw [show s.regs regLR = BitVec.ofNat 64 (s.regs 30).toNat by simp [GoABI.regLR]]
  refine reachesRet64_bind (entry_h1 s hpc hg hal h24 (by omega) hw) ?_
  rintro S hpc1 ⟨a0, a1, a2, a3, asp, a29, ak, am0, am1, am2, afr⟩
  have hsp' : S.sp.toNat = s.sp.toNat - 16 := by
    rw [asp, BitVec.toNat_sub]; simp; omega
  have hacc1 : S.mem.accessible (s.regs 0).toNat (s.regs 1).toNat true = true := by rw [afr.accessible]; exact hacc
  have hd1 : TabsOK S.mem := by
    refine hd.frame afr ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact accessible_sub hw (Or.inr rfl) (by omega) (by omega)
  have hstk : S.mem.accessible (S.sp.toNat - 8) 16 false = true := by
    rw [afr.accessible, hsp']; exact accessible_sub hw (Or.inl rfl) (by omega) (by omega)
  have hdl' : decLen (s.regs 3).toNat ≤ (s.regs 1).toNat := hdl
  refine reachesRet64_mono (outer (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat (s.regs 1).toNat (s.regs 29).toNat
    (s.regs 30).toNat hu64 hdl' (Nat.le_refl _) hp hret hret4 (s.regs 3).toNat 0 S (by simp) (by simpa using hdl') hacc1 hd1 hpc1
    (by rw [a0]; simp) (by rw [a2]; simp) (by rw [a1]; simp) (by rw [a3]; simp) (by rw [ak 30 (by simp)]; simp)
    (by rw [hsp']; omega) (by rw [hsp']; omega) (by rw [hsp']; omega) hstk
    (by rw [hsp']; omega) (by rw [hsp', show s.sp.toNat - 16 - 8 = s.sp.toNat - 24 by omega, am0])
    (by rw [hsp', am1]) (by intro k hk; omega) (Or.inr rfl)) ?_
  rintro S2 ⟨b0, bsp, b29, bk, bm, bfr, btab⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, btab⟩
  · rw [b0]
  · rw [bsp, asp]; exact BitVec.sub_add_cancel _ _
  · rw [b29]; simp
  · intro k hk
    rw [bk k hk, ak k (by simp only [Clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
  · exact bm
  · refine MemFrame.trans (rs := [((s.regs 0).toNat + (s.regs 1).toNat - decLen (s.regs 3).toNat, (s.regs 0).toNat + (s.regs 1).toNat),
        (s.sp.toNat - 24, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 16)]) (rs' := [((s.regs 0).toNat + (s.regs 1).toNat - decLen (s.regs 3).toNat, (s.regs 0).toNat + (s.regs 1).toNat - 0)])
      (afr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)) bfr (fun a n h => ?_)
    simp only [Outside, and_true] at h ⊢
    omega
end Fv256.Arm64.Dec
