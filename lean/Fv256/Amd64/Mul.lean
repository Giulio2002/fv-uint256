import Extracted
import Fv256.Spec.Mul
import Fv256.Spec.Util
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.Mul

/-!
# amd64: the compiled `(*uint256.Int).Mul` implements `Spec.mul`  (`Fv256/Spec/Mul.lean`)

`z.Mul(x, y)` (`RAX, RBX, RCX`) returns normally (no fault, no panic) with `RAX = z`, leaves `Spec.mul x y` (`x * y` modulo
`2^256`) in `z`, and writes only `z[0, 32)` and a 16-byte stack spill window. `z`, `x`, `y` may overlap arbitrarily.
The proof is `Fv256/Proofs/Amd64/Mul.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.Mul

/-- PRECONDITION (machine facts only). Stack: the window `[RSP-16, RSP+8)` (a 16-byte frame plus the return-address slot) is
writable. Buffers: `z` writable, `x`, `y` readable, 32 bytes each (they may alias each other freely); `z` avoids the whole
window, while `x` and `y` only avoid the frame `[RSP-16, RSP)` (reading the return-address slot is harmless). -/
def Pre (z x y : BitVec 64) (s : State) : Prop :=
  StackWritable s 16 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧
  Outside z 32 ((s.regs regSP).toNat - 16) ((s.regs regSP).toNat + 8) ∧
  Outside x 32 ((s.regs regSP).toNat - 16) (s.regs regSP).toNat ∧
  Outside y 32 ((s.regs regSP).toNat - 16) (s.regs regSP).toNat

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.mul` of the numbers at `x` and `y` BEFORE the call; memory changed
only in `z[0, 32)` and the 16-byte frame `[RSP-16, RSP)`. -/
def Post (z x y : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.mul (valueAt s x 32) (valueAt s y 32) ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 16) 16

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y] (Pre z x y) (Post z x y) :=
  correctness_proof z x y

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.Mul(x, x)`) satisfies `Pre` and its call returns with `Post`. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧ Pre z x y s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y s s' :=
  Wit.nonvacuous

/-- That concrete call returns `z` holding `0` (the memory it reads is all zero). -/
theorem returns : Returns (Extracted.program.withExit Wit.ret) Wit.s0 fun s' =>
    ABIReturn Wit.s0 s' ∧ s'.regs 0 = Wit.z ∧ valueAt s' Wit.z 32 = 0 :=
  Wit.returns

end Witness

end Fv256.Amd64.Mul
