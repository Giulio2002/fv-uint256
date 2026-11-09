import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.DecA
import Fv256.Proofs.Amd64.DecK
import Fv256.Proofs.Amd64.DecL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

set_option maxHeartbeats 16000000 in
/-- Summary of `internal/strconv.formatBase10(a []byte, u uint64) int`: `a[i:]` holds the decimal digits of `u`
(`i = len(a) - decLen u`, returned in `AX`); nothing else of `a` changes. -/
theorem fb10_summary :
    Summary Fv256.DecProg.program fb
      (fun s => (s.regs 0).toNat + (s.regs 3).toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (s.regs 3).toNat true = true ∧
        decLen (s.regs 7).toNat ≤ (s.regs 3).toNat ∧ 8 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 16 ≤ 2 ^ 48 ∧
        s.mem.accessible ((s.regs 4).toNat - 8) 24 true = true ∧ TabsOK s.mem ∧
        ((s.regs 0).toNat + (s.regs 3).toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 16 ≤ (s.regs 0).toNat) ∧
        s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
      (fun s s' => s'.regs 0 = BitVec.ofNat 64 ((s.regs 3).toNat - decLen (s.regs 7).toNat) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        (∀ k, k < decLen (s.regs 7).toNat →
          s'.mem.readLE ((s.regs 0).toNat + (s.regs 3).toNat - 1 - k) 1 = 48 + (s.regs 7).toNat / 10 ^ k % 10) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat + (s.regs 3).toNat - decLen (s.regs 7).toNat, (s.regs 0).toNat + (s.regs 3).toNat),
          ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] ∧
        TabsOK s'.mem) := by
  intro s hpc ⟨hp, hacc, hdl, hsp, hspu, hsa, hd, hdisj, hret⟩
  have hu64 := (s.regs 7).isLt
  have hs4 := (s.regs 4).isLt
  have hp0 := (s.regs 0).isLt
  have hn := (s.regs 3).isLt
  refine Fv256.E.reachesRet_bind (entry_h1 s hpc hsa hsp hspu hd) ?_
  rintro S ⟨R1, fl1, M1, rfl, a0, a3, a1, a7, a4, a5, ak, am0, am1, afr, hd1⟩
  have hacc1 : M1.accessible (s.regs 0).toNat (s.regs 3).toNat true = true := by
    rw [afr.accessible]; exact hacc
  have hsa1 : M1.accessible ((s.regs 4).toNat - 8) 16 true = true := by
    rw [afr.accessible]; exact accessible_sub hsa (Or.inr rfl) (by omega) (by omega)
  have t0 : BitVec.ofNat 64 (s.regs 0).toNat = s.regs 0 := by simp
  have t3 : BitVec.ofNat 64 (s.regs 3).toNat = s.regs 3 := by simp
  have t7 : BitVec.ofNat 64 (s.regs 7).toNat = s.regs 7 := by simp
  have t5 : BitVec.ofNat 64 (s.regs 5).toNat = s.regs 5 := by simp
  refine ReachesRet.mono (outer s (s.regs 0).toNat (s.regs 3).toNat (s.regs 7).toNat (s.regs 3).toNat
    ((s.regs 4).toNat - 8) (s.regs 5).toNat (s.mem.readLE (s.regs 4).toNat 8) hu64 hdl (Nat.le_refl _) hp (by omega)
    (by omega) hret (s.regs 7).toNat 0 R1 fl1 M1 (by simp) (by simpa using hdl) hacc1 hd1 hsa1 am0
    (by rw [show (s.regs 4).toNat - 8 + 8 = (s.regs 4).toNat by omega, am1]) (by rw [a0, t0]) (by rw [a3, Nat.sub_zero, t3])
    (by rw [a1, t3]) (by rw [a7, t7]) a4 (by intro k hk; omega) (Or.inr rfl)) ?_
  rintro S ⟨R2, fl2, M2, rfl, b0, b4, b5, bk, bm, bfr, bd⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact b0
  · show R2 4 = s.regs 4 + 8
    rw [b4, show (s.regs 4).toNat - 8 + 16 = (s.regs 4).toNat + 8 by omega]
    exact (bv_add_lit _ 8 (by omega)).symm
  · show R2 5 = s.regs 5
    rw [b5, t5]
  · show R2 14 = s.regs 14
    rw [bk 14 (by simp), ak 14 (by simp)]
  · exact bm
  · refine afr.trans bfr (rs'' := [((s.regs 0).toNat + (s.regs 3).toNat - decLen (s.regs 7).toNat, (s.regs 0).toNat + (s.regs 3).toNat),
          ((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)]) ?_
    intro a n h
    simp only [Outside, and_true] at h ⊢
    omega
  · exact bd
end Fv256.Amd64.Dec
