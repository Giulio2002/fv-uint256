import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).IAddUint64(n uint64) *Int` (arm64): in place, `z = z + n`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the 32 bytes at `z` are
writable, those at `x` readable (below `2^48`) and `z`, `x` are equal or disjoint, the call returns (no fault, no panic),
obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.addU` of the number at `x` before the call,
and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IAddUint64

theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => Ptr32 s.mem z true)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.addU (val256 s.mem z.toNat) n.toNat ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨hz, hz'⟩
  janus_intro hs
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); have := n.isLt; simp only [Spec.addU, Spec.W, Nat.reducePow]; omega))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true :=
  ⟨by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    Ptr32 s.mem z true :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  try decide

end Witness

end Fv256.Arm64.IAddUint64

