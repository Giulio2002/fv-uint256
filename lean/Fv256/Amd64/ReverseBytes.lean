import Extracted
import Fv256.Spec.ReverseBytes
import Fv256.Amd64.Machine
import Fv256.Proofs.Common.ReverseBytesBridge
import Fv256.Proofs.Amd64.ReverseBytes

/-!
# amd64: the compiled `(*uint256.Int).ReverseBytes` implements `Fv256.Spec.reverseBytes`  (`Fv256/Spec/ReverseBytes.lean`)

Calling `z.ReverseBytes(x)` with `z, x` in `RAX, RBX` returns normally (no fault, no panic) with `RAX = z`, leaves in `z` the number
`Fv256.Spec.reverseBytes x` (the 32 bytes of `x` in reverse order), and changes no byte outside `z[0, 32)`. `z` and `x` may coincide
but may not partially overlap.
The tactic proof is `Fv256/Proofs/Amd64/ReverseBytes.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.Amd64

namespace Fv256.Amd64.ReverseBytes

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` is a writable and `x` a readable 32-byte buffer; `z` does not overlap the return-address slot;
`z` and `x` are equal or disjoint. -/
def Pre (z x : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
  Disjoint z 32 (s.regs regSP) 8 ∧ Alias32 z x

/-- POSTCONDITION: `RAX = z`; the number now at `z` is `Spec.reverseBytes` of the number at `x` BEFORE the call; only `z[0, 32)` was written. -/
def Post (z x : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.reverseBytes (valueAt s x 32) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x) (Post z x) :=
  (correctness_proof z x).mono (fun _ h => h) fun s _ _ h =>
    ⟨h.1, h.2.1.trans (Fv256.ReverseBytesBridge.fromBE_32 s.mem x.toNat), h.2.2⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.ReverseBytes(x)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x s s' :=
  by
    obtain ⟨ret, s, z, x, hr, hc, hp, hret⟩ := Wit.nonvacuous
    exact ⟨ret, s, z, x, hr, hc, hp, hret.mono fun s' h =>
      ⟨h.1, h.2.1, h.2.2.1.trans (Fv256.ReverseBytesBridge.fromBE_32 s.mem x.toNat), h.2.2.2⟩⟩

end Witness

end Fv256.Amd64.ReverseBytes
