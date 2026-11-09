import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Arm64.MulModProg
import Fv256.Proofs.Arm64.MulModDefs
import Fv256.Proofs.Arm64.ReduceSpec
import Fv256.Proofs.Arm64.MulModSum

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.MulModSum

namespace Fv256.Arm64.MulModCorr

set_option maxRecDepth 200000 in
theorem hcSelf : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.MulModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem entry_eq : Fv256.Arm64.MulModSum.mulmodEntry = Extracted.entry := by decide

theorem correctness_param (hRec : Fv256.Arm64.MulModDefs.RecipSummaryU) (hR4 : Fv256.Arm64.ReduceSpec.R4Summary)
    (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => GuardOK s 768 ∧ s.sp.toNat % 16 = 0 ∧ 808 ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 808) (808 + 40) true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 808) 848 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧
        Apart z.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart x.toNat 32 (s.sp.toNat - 808) 848 ∧
        Apart y.toNat 32 (s.sp.toNat - 808) 848 ∧ Apart m.toNat 32 (s.sp.toNat - 808) 848)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 808, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 40)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ (entry_eq ▸ Janus.Contracts.EqHashModel.Summary.of_codeIn hcSelf (Fv256.Arm64.MulModSum.mulmod_summary hRec hR4)) ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, hzs, hxs, hys, hms⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    unfold Fv256.Arm64.MulModSum.pre
    rw [h30, h0, h1, h2, h3]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, ⟨hsal, hsb, hsc, hsw⟩, hgs, ⟨hz', hz, hzs⟩, ⟨hx', hx, hxs⟩, ⟨hy', hy, hys⟩, ⟨hm', hm, hms⟩⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, hzs, hxs, hys, hms⟩ s'
      ⟨hsp, h0', h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have e3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    simp only [e0, e1, e2, e3] at h0' hv hf
    refine ⟨⟨hsp, h28, h29, h18⟩, h0', ?_, hf⟩
    simpa only [val256] using hv

end Fv256.Arm64.MulModCorr
