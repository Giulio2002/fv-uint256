import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).IMul(x *Int) *Int` (arm64): in place, `z = z * x`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the stack-growth check
falls through (`GuardOK s 0`), the window `[SP-56, SP)` (the 56-byte frame) is writable and aligned (`StackOK s 56 0`), the 32
bytes at `z` are writable, those at `x` readable (below `2^48`), `z` and `x` are equal or disjoint, and neither overlaps the
frame window: the call returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is
`Fv256.Spec.mul` of the numbers at `z` and `x` before the call, and no byte outside `z[0..32)` and the frame window changes
(`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IMul

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x ∧
        Disjoint z.toNat 32 (s.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s.sp.toNat - 56) 56)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.mul (val256 s.mem z.toNat) (val256 s.mem x.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx, hd1, hd2⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2
  rcases hzx with rfl | hzx
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); refine ⟨?_, ?_⟩; (· simp only [Spec.mul, Spec.W, Nat.reducePow]; janus_arith); (· simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff])))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 56 0 ∧ Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 56) 56 :=
  ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    Or.inr (by unfold Disjoint32 Disjoint z x; decide), by unfold Disjoint; decide, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x ∧
      Disjoint z.toNat 32 (s.sp.toNat - 56) 56 ∧ Disjoint x.toNat 32 (s.sp.toNat - 56) 56) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat = Spec.mul (val256 s0.mem z.toNat) (val256 s0.mem x.toNat) ∧
      Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 (s0.sp.toNat - 56) 56 :=
  correctness z x ret hret s0 setup hpre

end Witness

end Fv256.Arm64.IMul
