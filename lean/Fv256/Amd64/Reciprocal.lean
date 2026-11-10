import Extracted
import Fv256.Spec.Reciprocal
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Reciprocal

/-!
# amd64: the compiled `uint256.Reciprocal` implements `Spec.IsReciprocal`  (`Fv256/Spec/Reciprocal.lean`)

`Reciprocal(m)` (`m` in `RAX`) returns normally (no fault, no panic) and leaves the five result limbs (40 bytes, least significant
first) at `RSP+8` (the callee's result slot), where they form a number `mu` with `Spec.IsReciprocal m mu`: zero for `m < 2^192`,
within three units below `⌊(2^512 - 1) / m⌋` otherwise (within one unit for `m >= 2^193`). It writes only its stack window.
The proof is `Fv256/Proofs/Amd64/Reciprocal.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Reciprocal

/-- PRECONDITION (machine facts only). Stack: the stack-growth check falls through (`StackGuardOK`), at least `0x248` bytes of
stack exist, and the window `[RSP-0x240, RSP+0x30)` (frame plus the result slot) is writable. `m` is a readable 32-byte buffer;
neither `m` nor the goroutine's `stackguard0` word (at `R14 + 16`) overlaps the window `[RSP-0x240, RSP+0x30)` extended to 0x270 bytes. -/
def Pre (m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x1b8 ∧ 0x248 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x240 0x30 ∧ Buffer s m 32 false ∧
  Apart m.toNat 32 ((s.regs regSP).toNat - 0x240) 0x270 ∧
  Apart ((s.regs regG).toNat + 16) 8 ((s.regs regSP).toNat - 0x240) 0x270

/-- POSTCONDITION: the 320-bit number at `RSP+8` after the call is an acceptable `Reciprocal` of the number at `m` BEFORE the
call (`Spec.IsReciprocal`); memory changed only in the window `[RSP-0x240, RSP+0x30)`. -/
def Post (m : BitVec 64) (s s' : State) : Prop :=
  Fv256.Spec.IsReciprocal (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40) ∧
  MemFrame s.mem s'.mem [((s.regs regSP).toNat - 0x240, (s.regs regSP).toNat + 0x30)]

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

/-- That concrete call (`m = 0`, below `2^192`) leaves the zero reciprocal in the result slot. -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.mem.readLE ((Wit.s0.regs regSP).toNat + 8) 40 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Reciprocal
