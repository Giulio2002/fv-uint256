import Extracted
import Fv256.Spec.Reciprocal
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.Reciprocal

/-!
# arm64: the compiled `uint256.Reciprocal` implements `Spec.IsReciprocal`  (`Fv256/Spec/Reciprocal.lean`)

`Reciprocal(m)` (`m` in `X0`) returns normally (no fault, no panic) and leaves the five result limbs (40 bytes, least significant
first) at `SP+8` (the callee's result slot), where they form a number `mu` with `Spec.IsReciprocal m mu`: zero for `m < 2^192`,
within three units below `⌊(2^512 - 1) / m⌋` otherwise (within one unit for `m >= 2^193`). It writes only its own stack frame.
The proof is `Fv256/Proofs/Arm64/Reciprocal.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Reciprocal

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`GuardOK`), a `0x118`-byte frame plus the
`0x30` bytes above `SP` are usable (`StackOK`), and the goroutine's `stackguard0` word (at `X28`) is outside the frame.
`m` is a readable 32-byte buffer not overlapping the frame `[SP-0x118, SP+0x30)`. -/
def Pre (m : BitVec 64) (s : State) : Prop :=
  GuardOK s 0x90 ∧ StackOK s 0x118 0x30 ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 0x118 ∨ s.sp.toNat + 0x30 ≤ (s.regs 28).toNat + 16) ∧
  Ptr32 s.mem m false ∧ Janus.Spec.Disjoint m.toNat 32 (s.sp.toNat - 0x118) 0x148

/-- POSTCONDITION: the 320-bit number at `SP+8` after the call is an acceptable `Reciprocal` of the number at `m` BEFORE the
call (`Spec.IsReciprocal`); memory changed only in the frame `[SP-0x118, SP-8)` and the result slot `[SP+8, SP+0x30)`. -/
def Post (m : BitVec 64) (s s' : State) : Prop :=
  Fv256.Spec.IsReciprocal (val256 s.mem m.toNat) (s'.mem.readLE (s.sp.toNat + 8) 40) ∧
  MemFrame s.mem s'.mem [(s.sp.toNat - 0x118, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 0x30)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m] (Pre m) (Post m) :=
  ensures_mono_post (correctness_proof m) (post_bridge m)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s ∧ Pre m s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post m s s' :=
  let ⟨ret, s, m, h1, h2, h3, h4⟩ := Wit.nonvacuous
  ⟨ret, s, m, h1, h2, h3, h4.mono fun s' h => ⟨h.1, post_bridge m s s' h.2⟩⟩

end Witness

end Fv256.Arm64.Reciprocal
