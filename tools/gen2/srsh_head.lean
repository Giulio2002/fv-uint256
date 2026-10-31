import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SRsh(x *Int, n uint) *Int` (arm64): arithmetic shift right, `z = x >> n` (sign-propagating)

**Guarantee.** For every pointer `z` (receiver, `X0`) and `x` (`X1`) and shift count `n` (`X2`, any 64-bit value), every Go call
whose stack-growth check falls through (`GuardOK s 0`) and whose stack window `[SP-56, SP)` is writable and aligned
(`StackOK s 56 0`): if the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` and `x` are equal or disjoint, and
neither overlaps the stack window, then the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at
`z` afterwards is `Fv256.Spec.srsh` of the number at `x` before the call (the two's-complement reading of `x` shifted right by `n`
with sign fill, i.e. `~(~x >> n)` for negative `x`; counts of 256 or more give 0 or all ones), and no byte changes outside
`z[0..32)` and the stack window (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns `z` holding the result.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SRsh

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (z x n : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s)
    (hg : GuardOK s 0) (hst : StackOK s 56 0) :
    (Ptr32 s.mem z true → Ptr32 s.mem x false → Aliasing z x →
      Disjoint z.toNat 32 (s.sp.toNat - 56) 56 → Disjoint x.toNat 32 (s.sp.toNat - 56) 56 →
      Returns (Extracted.program.withExit ret) s (fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.srsh (val256 s.mem x.toNat) n.toNat ∧
          Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56)) := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hb, ha, hw⟩ := hst
  janus_intro hs
  intro ⟨hz, hz'⟩ ⟨hx, hx'⟩ hzx hd1 hd2
  rcases hzx with rfl | hzx
  · @@Z@@  · @@X@@

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem hg : GuardOK s0 0 := by unfold GuardOK; decide
theorem hst : StackOK s0 56 0 := by unfold StackOK; decide

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 56) 56 :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide),
    by unfold Disjoint; decide, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, n] s ∧ GuardOK s 0 ∧ StackOK s 56 0 ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x ∧
      Disjoint z.toNat 32 (s.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s.sp.toNat - 56) 56) :=
  ⟨ret, s0, z, x, n, hret, setup, hg, hst, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x n ret hret s0 setup hg hst hpre.1 hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hpre.2.2.2.2).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.SRsh
