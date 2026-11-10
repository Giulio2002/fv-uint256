import Extracted
import Fv256.Spec.IAddMod
import Fv256.Proofs.Arm64.IAddMod

/-!
# arm64: the compiled `(*uint256.Int).IAddMod` implements `Spec.iAddMod`  (`Fv256/Spec/IAddMod.lean`)

`z.IAddMod(x, m)` (`X0, X1, X2`) returns normally (no fault, no panic) with `X0` = z, leaves `Fv256.Spec.iAddMod z x m`
(that is `(z + x) mod m`, or `0` for `m = 0`, with `z` the receiver's value before the call) in `z`, and writes only `z[0,
32)` and the callee's stack frame. The callee `AddMod` is used through its verified library summary.
The tactic proof is `Fv256/Proofs/Arm64/IAddMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IAddMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned with
the frame `[SP-904, SP-32)` accessible for writing, and the binary's read-only data is loaded. Buffers: `z` writable, `x`,
`m` readable, 32 bytes each, none overlapping the frame; `z` is equal-or-disjoint from `x` and from `m`; the goroutine's
`g` words at `X28` are outside the frame and do not overlap `z`. -/
def Pre (z x m : BitVec 64) (s : State) : Prop :=
  GuardOK s 864 ∧ s.sp.toNat % 16 = 0 ∧ 904 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 904) 872 true = true ∧ Extracted.program.DataLoaded s.mem ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 904 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 904) 872 ∧ Disjoint x.toNat 32 (s.sp.toNat - 904) 872 ∧
  Disjoint m.toNat 32 (s.sp.toNat - 904) 872 ∧
  (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
  (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
  ((s.regs 28).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16)

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.iAddMod` of the numbers at `z`, `x`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.iAddMod (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 904, s.sp.toNat - 32)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m) (Post z x m) :=
  correctness_proof z x m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IAddMod(x, x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧ Pre z x m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.IAddMod
