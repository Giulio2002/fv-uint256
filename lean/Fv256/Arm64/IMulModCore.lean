import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.CodeIn
import Fv256.Arm64.MulModProg
import Fv256.Arm64.MulModDefs
import Fv256.Arm64.ReduceSpec
import Fv256.Arm64.MulModSum

/-!
# `(*uint256.Int).IMulMod(x, m *Int) *Int` (arm64): in place, `z = (z * x) mod m`   (core: conditional on the callee summaries)

`IMulMod` is `z.MulMod(z, x, m)`; the callee is used through `Fv256.Arm64.MulModSum.mulmod_summary` over `Fv256.Arm64.MulModProg.program`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IMulModCore

set_option maxRecDepth 200000 in
theorem hcMM : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.MulModProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev Pre (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 816 ∧
  (s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 856) 856 true = true) ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 856) 856 ∧
  ((s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧ Apart (s.regs 0).toNat 32 (s.sp.toNat - 856) 856) ∧
  ((s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 856) 856) ∧
  ((s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧ Apart (s.regs 2).toNat 32 (s.sp.toNat - 856) 856)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem imulmod_summary (hRec : Fv256.Arm64.MulModDefs.RecipSummaryU) (hR4 : Fv256.Arm64.ReduceSpec.R4Summary) :
    Summary Extracted.program Extracted.entry Pre
    (fun s s' => s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 0).toNat 32)
          (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hsal, hsb, hsc, hsw⟩, hgs, ⟨hzb, hza, hzs⟩, ⟨hxb, hxa, hxs⟩, ⟨hmb, hma, hms⟩⟩
  janus_run [Util.readLE_32] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcMM (Fv256.Arm64.MulModSum.mulmod_summary hRec hR4)]
  refine ⟨by janus_assumption, ?_⟩
  janus_frame


theorem correctness_param (hRec : Fv256.Arm64.MulModDefs.RecipSummaryU) (hR4 : Fv256.Arm64.ReduceSpec.R4Summary)
    (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m]
      (fun s => GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
        s.mem.accessible (s.sp.toNat - 856) 856 true = true ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 856) 856 ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
        Apart z.toNat 32 (s.sp.toNat - 856) 856 ∧ Apart x.toNat 32 (s.sp.toNat - 856) 856 ∧
        Apart m.toNat 32 (s.sp.toNat - 856) 856)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.F.mulmodSpec (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ (imulmod_summary hRec hR4) ?_ ?_
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hm, hm'⟩, hzs, hxs, hms⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = m := by have := hsu.args 2 (by simp); simpa using this
    unfold Pre
    rw [h30, h0, h1, h2]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, ⟨hsal, hsb, hsc, hsw⟩, hgs, ⟨hz', hz, hzs⟩, ⟨hx', hx, hxs⟩, ⟨hm', hm, hms⟩⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
  · intro ret hret s hsu ⟨hg, hsal, hsb, hsc, hsw, hgs, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hm, hm'⟩, hzs, hxs, hms⟩ s'
      ⟨hsp, h0', h18, h28, h29, h30, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = m := by have := hsu.args 2 (by simp); simpa using this
    simp only [e0, e1, e2] at h0' hv hf
    refine ⟨⟨hsp, h28, h29, h18⟩, h0', ?_, hf⟩
    simpa only [val256] using hv

end Fv256.Arm64.IMulModCore
