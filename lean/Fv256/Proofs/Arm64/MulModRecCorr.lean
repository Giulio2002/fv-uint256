import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Arm64.MulModRecProg
import Fv256.Proofs.Arm64.MulModDefs
import Fv256.Proofs.Arm64.ReduceSpec
import Fv256.Proofs.Arm64.MulModRecSum

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.MulModRecSum

namespace Fv256.Arm64.MulModRecCorr

set_option maxRecDepth 200000 in
theorem hcSelf : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.MulModRecProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem entry_eq : Fv256.Arm64.MulModRecSum.mulmodrecEntry = Extracted.entry := by decide

theorem correctness_param (hR4 : Fv256.Arm64.ReduceSpec.R4Summary)
    (z x y m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m, mu]
      (fun s => GuardOK s 720 ∧ s.sp.toNat % 16 = 0 ∧ 760 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 760) (760 + 48) true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 760) 808 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m false ∧ (mu.toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible mu.toNat 40 false = true) ∧
        Apart z.toNat 32 (s.sp.toNat - 760) 808 ∧ Apart x.toNat 32 (s.sp.toNat - 760) 808 ∧
        Apart y.toNat 32 (s.sp.toNat - 760) 808 ∧ Apart m.toNat 32 (s.sp.toNat - 760) 808 ∧
        Apart mu.toNat 40 (s.sp.toNat - 760) 808 ∧
        Fv256.F.MuOK (val256 s.mem m.toNat) (s.mem.readLE mu.toNat 40))
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 760, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 48)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ (entry_eq ▸ Janus.Contracts.EqHashModel.Summary.of_codeIn hcSelf (Fv256.Arm64.MulModRecSum.mulmodrec_summary hR4)) ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, ⟨hq', hq⟩, hzs, hxs, hys, hms, hus, hmu⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have h3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    have h4 : s.regs 4 = mu := by have := hsu.args 4 (by simp); simpa using this
    unfold Fv256.Arm64.MulModRecSum.pre
    rw [h30, h0, h1, h2, h3, h4]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, ⟨hsal, hsb, hsc, hsw⟩, hgs, ⟨hz', hz, hzs⟩, ⟨hx', hx, hxs⟩, ⟨hy', hy, hys⟩, ⟨hm', hm, hms⟩, ⟨hq', hq, hus⟩, by simpa only [val256] using hmu⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hm, hm'⟩, ⟨hq', hq⟩, hzs, hxs, hys, hms, hus, hmu⟩ s'
      ⟨hsp, h0', h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    have e3 : s.regs 3 = m := by have := hsu.args 3 (by simp); simpa using this
    have e4 : s.regs 4 = mu := by have := hsu.args 4 (by simp); simpa using this
    simp only [e0, e1, e2, e3, e4] at h0' hv hf
    refine ⟨⟨hsp, h28, h29, h18⟩, h0', ?_, hf⟩
    simpa only [val256] using hv

end Fv256.Arm64.MulModRecCorr
