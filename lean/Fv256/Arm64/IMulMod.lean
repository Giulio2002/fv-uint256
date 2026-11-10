import Extracted
import Fv256.Spec.IMulMod
import Fv256.Proofs.Arm64.IMulMod

/-!
# arm64: the compiled `(*uint256.Int).IMulMod` implements `Spec.iMulMod`  (`Fv256/Spec/IMulMod.lean`)

`z.IMulMod(x, m)` (`X0, X1, X2`) returns normally (no fault, no panic) with `X0` = z, leaves `Fv256.Spec.iMulMod z x m`
(that is `(z * x) mod m`, or `0` for `m = 0`, with `z` the receiver's value before the call) in `z`, and writes only `z[0,
32)` and its own stack frame. `z`, `x`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Arm64/IMulMod.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.IMulMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned and
the frame `[SP-856, SP)` is accessible for writing. Buffers: `z` writable, `x`, `m` readable, 32 bytes each (they may
alias each other freely), none overlapping the frame (`Apart`); the goroutine's `g` word at `X28+16` is outside it. -/
def Pre (z x m : BitVec 64) (s : State) : Prop :=
  GuardOK s 816 ∧ s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 856) 856 true = true ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 856) 856 ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem m false ∧
  Apart z.toNat 32 (s.sp.toNat - 856) 856 ∧ Apart x.toNat 32 (s.sp.toNat - 856) 856 ∧
  Apart m.toNat 32 (s.sp.toNat - 856) 856

/-- POSTCONDITION: `X0 = z`; the number at `z` is `Spec.iMulMod` of the numbers at `z`, `x`, `m` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  val256 s'.mem z.toNat = Fv256.Spec.iMulMod (val256 s.mem z.toNat) (val256 s.mem x.toNat) (val256 s.mem m.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 856, s.sp.toNat - 8)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m) (Post z x m) :=
  correctness_proof z x m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IMulMod(x, m)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m] s ∧ Pre z x m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.IMulMod
