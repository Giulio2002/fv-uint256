import Extracted
import Fv256.Spec.ISMod
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.ISMod

/-!
# arm64: the compiled `(*uint256.Int).ISMod` implements `Spec.ismod`  (`Fv256/Spec/ISMod.lean`)

`z.ISMod(x)` (`X0, X1`) returns normally (no fault, no panic, also for a zero divisor) with `X0 = z`, leaves `Spec.ismod z x` (the signed remainder of the old `z`, sign of `z`; `0` when `x = 0`)
in `z`, and writes only `z[0, 32)` and its own stack frame. `z` and `x` may overlap arbitrarily.
The proof is `Fv256/Proofs/Arm64/ISMod.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ISMod

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), `SP` is 16-byte aligned and
inside the user address space, and the 616-byte window `[SP-648, SP-32)` below it is writable; the goroutine's
`stackguard0` word (at `X28`) is outside that window. Buffers: `z` writable, `x` readable, 32 bytes each (they may alias each
other), neither overlapping the window. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  GuardOK s 608 ∧ s.sp.toNat % 16 = 0 ∧ 648 ≤ s.sp.toNat ∧ s.sp.toNat ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 648) 616 true = true ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 648 ∨ s.sp.toNat - 32 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 648) 616 ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 648) 616

/-- POSTCONDITION: `X0 = z`; the number now at `z` is `Spec.ismod` of the numbers at `z` and `x` BEFORE the call; memory
changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  Janus.Spec.val256 s'.mem z.toNat = Fv256.Spec.ismod (Janus.Spec.val256 s.mem z.toNat) (Janus.Spec.val256 s.mem x.toNat) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat - 648, s.sp.toNat - 32)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  correctness_proof z x

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.ISMod
