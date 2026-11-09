import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.RecipSpec
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Arm64.RecipSummary

/-!
# `uint256.Reciprocal(m *Int) (mu [5]uint64)` (arm64)

**Documented behaviour.** "Reciprocal computes a 320-bit value representing 1/m", specialised to `m[3] != 0` (so
`2^192 <= m < 2^256`), "returns zero if `m[3] == 0`".  The five result words are returned in the caller's result slot (`SP+8` on entry).

**Guarantee.** For every `m` with 32 readable bytes (below `2^48`) outside the callee window, and every Go call in which the
stack-growth check falls through, the call returns, and with `M` the number at `m` and `mu` the 320-bit result:
`M < 2^192` gives `mu = 0`; `2^192 <= M` gives `RecipWeak M mu` (`ex-3 <= mu <= ex`, `ex = (2^512-1)/M`); `2^193 <= M` gives
`RecipOK M mu` (`ex-1 <= mu <= ex`).  Nothing outside the frame window changes.

Derived from `Fv256.Arm64.RecipSeg.recip_summary` (the compiled `Reciprocal` with `Lsh` inlined).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Reciprocal

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.RecipProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

theorem recip_summary_ex : Summary Extracted.program Extracted.entry Fv256.Arm64.RecipSeg.RecPre Fv256.Arm64.RecipSeg.RecSpec :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain Fv256.Arm64.RecipSeg.recip_summary

theorem correctness (m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m]
      (fun s => GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem m false ∧ Disjoint m.toNat 32 (s.sp.toNat - 0x118) 0x148)
      (fun s s' =>
        (val256 s.mem m.toNat < 2 ^ 192 → s'.mem.readLE (s.sp.toNat + 8) 40 = 0) ∧
        (2 ^ 192 ≤ val256 s.mem m.toNat → Fv256.F.RecipWeak (val256 s.mem m.toNat) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
        (2 ^ 193 ≤ val256 s.mem m.toNat → Fv256.F.RecipOK (val256 s.mem m.toNat) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 0x118, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 0x30)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ recip_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hgw, ⟨hm, hm'⟩, hdm⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = m := by have := hsu.args 0 (by simp); simpa using this
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hgw, ?_, ?_, ?_⟩
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h30]; simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · rw [h0]; exact hm'
    · rw [h0]; exact hm
    · rw [h0]; simp only [Disjoint] at hdm; omega
  · intro ret hret s hsu ⟨hg, hs, hgw, ⟨hm, hm'⟩, hdm⟩ s' ⟨hsp, h18, h28, h29, h30, hf, hz, hw, hok⟩
    have h0 : s.regs 0 = m := by have := hsu.args 0 (by simp); simpa using this
    rw [h0] at hz hw hok
    exact ⟨⟨hsp, h28, h29, h18⟩, hz, hw, hok, hf⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def m : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then m else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    subst h; rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 0x90 ∧ StackOK s0 0x118 0x30 ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 0x118 ∨ s0.sp.toNat + 0x30 ≤ (s0.regs 28).toNat + 16) ∧
    Ptr32 s0.mem m false ∧ Disjoint m.toNat 32 (s0.sp.toNat - 0x118) 0x148 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide, ⟨by decide, by decide⟩, ?_⟩
  unfold Disjoint; decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s ∧
    (GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
      Ptr32 s.mem m false ∧ Disjoint m.toNat 32 (s.sp.toNat - 0x118) 0x148) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (val256 s.mem m.toNat < 2 ^ 192 → s'.mem.readLE (s.sp.toNat + 8) 40 = 0) ∧
        (2 ^ 192 ≤ val256 s.mem m.toNat → Fv256.F.RecipWeak (val256 s.mem m.toNat) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
        (2 ^ 193 ≤ val256 s.mem m.toNat → Fv256.F.RecipOK (val256 s.mem m.toNat) (s'.mem.readLE (s.sp.toNat + 8) 40)) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 0x118, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 0x30)] :=
  ⟨ret, s0, m, hret, setup, hpre,
    correctness m ret hret s0 setup hpre⟩

end Witness

end Fv256.Arm64.Reciprocal
