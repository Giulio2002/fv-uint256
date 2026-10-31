import Extracted
import Fv256.Spec

/-!
# `(*uint256.Int).IsZero() bool` (arm64)

**Guarantee.** For every pointer `x` and every Go call state of the compiled method with `x` in
`X0` such that the 32 bytes at `x` are readable (inside one caller region, below `2^48`), the call
returns (never faulting or panicking), obeys the ABI, and the `bool` result (low byte of `X0`)
is `1` iff the 256-bit little-endian value at `x` is `0` (`Fv256.Spec.isZero`).

**Non-vacuity.** `Witness.nonvacuous`: the precondition holds for a concrete call state;
`Witness.returns`: that call returns `true` (the zero array).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts.Mem

namespace Fv256.Arm64.IsZero

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (fun s => Ptr32 s.mem x false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.isZero (val256 s.mem x.toNat)).toNat) := by
  intro ret hret s hs ⟨hx, hx'⟩
  janus_intro hs
  sorry

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 28 then BitVec.ofNat 64 wg
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem x false := ⟨by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Ptr32 s.mem x false :=
  ⟨ret, s0, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Witness

end Fv256.Arm64.IsZero
