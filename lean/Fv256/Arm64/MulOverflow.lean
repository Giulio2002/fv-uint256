import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.MoCases.A
import Fv256.Arm64.MoCases.B
import Fv256.Arm64.MoCases.C
import Fv256.Arm64.MoCases.D
import Fv256.Arm64.MoCases.E

/-!
# `(*uint256.Int).MulOverflow(x, y *Int) (*Int, bool)` (arm64): `z = x * y mod 2^256` and the overflow flag

**Guarantee.** For all pointers `z`, `x`, `y` (`X0` receiver, `X1`, `X2`) with the 32 bytes at `z` writable and those at `x`, `y` readable
(below `2^48`), every pair of the three pointers equal or disjoint, the 256-byte window below the stack pointer (`StackOK s 240 16`: the
function's frame and the extracted `umul` callee's) disjoint from the three objects, and a Go call whose stack check falls through
(`GuardOK s 0`): the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the overflow flag in `X1` is `1` iff
`x*y >= 2^256`, the number at `z` afterwards is `Fv256.Spec.mul` of the numbers at `x` and `y` before the call, and no byte changes outside
`z[0..32)` and the stack window. One proof module per aliasing pattern of `(z, x, y)` (`MoCases/A..E`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with flag `0` and value `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MulOverflow

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
        Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
        Disjoint y.toNat 32 (s.sp.toNat - 240) 256)
      (fun s s' => s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256) := by
  intro ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩
  rcases hzx with hzx | hzx
  · subst hzx
    rcases hzy with hzy | hzy
    · subst hzy
      exact caseE _ ret hret s hs ⟨hg, hst, hz, hx, hy, hd1⟩
    · exact caseB _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzy, hd1, hd3⟩
  · rcases hzy with hzy | hzy
    · subst hzy
      exact caseC _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
    · rcases hxy with hxy | hxy
      · subst hxy
        exact caseD _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hd1, hd2⟩
      · exact caseA _ _ _ ret hret s hs ⟨hg, hst, hz, hx, hy, hzx, hzy, hxy, hd1, hd2, hd3⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

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

theorem hpre : GuardOK s0 0 ∧ StackOK s0 240 16 ∧ Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Aliasing z x ∧ Aliasing z x ∧ Aliasing x x ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 240) 256 ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 240) 256 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inl rfl,
    by unfold Disjoint z; decide, by unfold Disjoint x; decide, by unfold Disjoint x; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (GuardOK s 0 ∧ StackOK s 240 16 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
      Aliasing z x ∧ Aliasing z y ∧ Aliasing x y ∧
      Disjoint z.toNat 32 (s.sp.toNat - 240) 256 ∧ Disjoint x.toNat 32 (s.sp.toNat - 240) 256 ∧
      Disjoint y.toNat 32 (s.sp.toNat - 240) 256) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        (s'.regs 1).toNat = (if Spec.W ≤ val256 s.mem x.toNat * val256 s.mem y.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 240) 256 :=
  ⟨ret, s0, z, x, x, hret, setup, hpre,
    correctness z x x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ (s'.regs 1).toNat = 0 ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_, ?_⟩
  · rw [h.2.2.1]; decide
  · rw [h.2.2.2.1]; decide

end Witness

end Fv256.Arm64.MulOverflow
