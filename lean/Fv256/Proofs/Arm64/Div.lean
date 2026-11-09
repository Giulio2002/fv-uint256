import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Arm64.SummaryEnsures
import Fv256.Proofs.Arm64.DivSum
import Fv256.Proofs.Arm64.CodeIn
import Fv256.Proofs.Arm64.DivProg

/-!
# `(*uint256.Int).Div(x, y *Int) *Int` (arm64): `z = x / y` (`0` when `y = 0`)

**Guarantee.** For all pointers `z` (receiver, `X0`), `x` (`X1`), `y` (`X2`) with the 32 bytes at `z` writable and
those at `x`, `y` readable (below `2^48`; they may be equal or overlap arbitrarily), outside the callee's stack window,
and a stack with room for the frame and the stack-growth check passing, the call returns (no fault, no panic), obeys
the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.B.divSpec` of the numbers at `x` and `y` before
the call, and nothing changes outside `z[0..32)` and the callee's stack frame.

Derived from `Fv256.Arm64.DivSum.div_summary` (the compiled `Div` with `udivrem` as a verified callee).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Div

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.DivProg.program Extracted.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem div_summary_ex : Summary Extracted.program Extracted.entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 416 ∧ StackOK s 456 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
        (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
        (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
        ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
        ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.divSpec (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 2).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 456, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 16)]) :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain Fv256.Arm64.DivSum.div_summary

theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => GuardOK s 416 ∧ StackOK s 456 16 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 456) 472 ∧ Disjoint x.toNat 32 (s.sp.toNat - 456) 472 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 456) 472)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 456, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 16)]) := by
  refine Fv256.Arm64.SummaryEnsures.ensures_of_summary _ _ div_summary_ex ?_ ?_
  · intro ret hret s hsu ⟨hg, hs, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hdz, hdx, hdy⟩
    have h30 : s.regs 30 = BitVec.ofNat 64 ret := by
      have := hsu.lr; exact this
    have h0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have h1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have h2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    rw [h30, h0, h1, h2]
    have ha := hret.aligned
    have hu := hret.user
    refine ⟨?_, ?_, hg, hs, hgw, hz', hz, hx', hx, hy', hy, ?_, ?_, ?_⟩
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [show ret % 2 ^ 64 = ret from Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [Disjoint] at hdz; omega
    · simp only [Disjoint] at hdx; omega
    · simp only [Disjoint] at hdy; omega
  · intro ret hret s hsu ⟨hg, hs, hgw, ⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hdz, hdx, hdy⟩ s' ⟨hpc, hsp, h0, h18, h28, h29, h30, hr, hv, hf⟩
    have e0 : s.regs 0 = z := by have := hsu.args 0 (by simp); simpa using this
    have e1 : s.regs 1 = x := by have := hsu.args 1 (by simp); simpa using this
    have e2 : s.regs 2 = y := by have := hsu.args 2 (by simp); simpa using this
    rw [e0, e1, e2] at hv
    rw [e0] at hf h0
    refine ⟨⟨hsp, h28, h29, h18⟩, ?_, ?_, hf⟩
    · exact h0
    · exact hv

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

set_option maxRecDepth 200000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 416 ∧ StackOK s0 456 16 ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 456 ∨ s0.sp.toNat + 16 ≤ (s0.regs 28).toNat + 16) ∧
    Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 456) 472 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 456) 472 ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 456) 472 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_⟩ <;>
    (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (GuardOK s 416 ∧ StackOK s 456 16 ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 456 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
      Disjoint z.toNat 32 (s.sp.toNat - 456) 472 ∧ Disjoint x.toNat 32 (s.sp.toNat - 456) 472 ∧
      Disjoint y.toNat 32 (s.sp.toNat - 456) 472) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 456, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 16)] :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

end Witness

end Fv256.Arm64.Div
