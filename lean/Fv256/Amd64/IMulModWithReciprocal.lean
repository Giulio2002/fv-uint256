import Extracted
import Fv256.Spec.IMulModWithReciprocal
import Fv256.Proofs.Amd64.IMulModWithReciprocal

/-!
# amd64: the compiled `(*uint256.Int).IMulModWithReciprocal` implements `Spec.iMulModWithReciprocal`  (`Fv256/Spec/IMulModWithReciprocal.lean`)

`z.IMulModWithReciprocal(x, m, mu)` (`RAX, RBX, RCX, RDI`) returns normally (no fault, no panic) with `RAX` = z, leaves
`Fv256.Spec.iMulModWithReciprocal z x m` (that is `(z * x) mod m`, or `0` for `m = 0`, with `z` the receiver's value
before the call) in `z`, and writes only `z[0, 32)` and its own stack frame, PROVIDED `mu` is a valid reciprocal of `m`
(`Fv256.Spec.muOk`, a runtime-contract hypothesis of the Go API). `z`, `x`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/IMulModWithReciprocal.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMulModWithReciprocal

/-- PRECONDITION (machine facts only, plus one runtime contract). Stack: the stack-growth check falls through
(`StackGuardOK`), enough stack exists, and the window `[RSP-0x320, RSP+0x8)` is writable. Buffers: `z` writable, `x`, `m`
readable 32-byte buffers and `mu` a readable 40-byte buffer (the 5-word reciprocal), none overlapping the window
(`Apart`); the goroutine's `g` word at `R14+16` is outside the window. Runtime contract (Go API): `Fv256.Spec.muOk` says
`mu` is a valid reciprocal of `m`. -/
def Pre (z x m : BitVec 64) (mu : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x2d0 ∧ 0x328 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x320 8 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
  Apart z.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
  Apart x.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
  Apart m.toNat 32 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
      Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x320) 0x328 ∧
      Fv256.Spec.muOk (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
  Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x320) 0x328

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.iMulModWithReciprocal` of the numbers at `z`, `x`, `m` BEFORE the
call; memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x m : BitVec 64) (mu : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.iMulModWithReciprocal (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x320, (s.regs regSP).toNat)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x m : BitVec 64) (mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m, mu] (Pre z x m mu) (Post z x m mu) :=
  correctness_proof z x m mu

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.IMulModWithReciprocal(x, m, mu)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, m, mu] s ∧ Pre z x m mu s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x m mu s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.IMulModWithReciprocal
