import Extracted
import Fv256.Spec.MulModWithReciprocal
import Fv256.Proofs.Amd64.MulModWithReciprocal

/-!
# amd64: the compiled `(*uint256.Int).MulModWithReciprocal` implements `Spec.mulModWithReciprocal`  (`Fv256/Spec/MulModWithReciprocal.lean`)

`z.MulModWithReciprocal(x, y, m, mu)` (`RAX, RBX, RCX, RDI, RSI`) returns normally (no fault, no panic) with `RAX` = z,
leaves `Fv256.Spec.mulModWithReciprocal x y m` (that is `(x * y) mod m`, or `0` for `m = 0`) in `z`, and writes only `z[0,
32)` and its own stack frame, PROVIDED `mu` is a valid reciprocal of `m` (`Fv256.Spec.muOk`, a runtime-contract hypothesis
of the Go API). `z`, `x`, `y`, `m` may overlap arbitrarily.
The tactic proof is `Fv256/Proofs/Amd64/MulModWithReciprocal.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModWithReciprocal

/-- PRECONDITION (machine facts only, plus one runtime contract). Stack: the stack-growth check falls through
(`StackGuardOK`), enough stack exists, and the window `[RSP-0x2e8, RSP+0x30)` is writable. Buffers: `z` writable, `x`,
`y`, `m` readable 32-byte buffers and `mu` a readable 40-byte buffer (the 5-word reciprocal), none overlapping the window
(`Apart`); the goroutine's `g` word at `R14+16` is outside the window. Runtime contract (Go API): `Fv256.Spec.muOk` says
`mu` is a valid reciprocal of `m`. -/
def Pre (z x y m mu : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x298 ∧ 0x2f0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x2e8 0x30 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧ Buffer s mu 40 false ∧
  Apart z.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
  Apart x.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
  Apart y.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
  Apart m.toNat 32 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
  Apart mu.toNat 40 (((s.regs regSP).toNat) - 0x2e8) 0x318 ∧
  Fv256.Spec.muOk (valueAt s m 32) (s.mem.readLE mu.toNat 40) ∧
  Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x2e8) 0x318

/-- POSTCONDITION: `RAX = z`; the number at `z` is `Spec.mulModWithReciprocal` of the numbers at `x`, `y`, `m` BEFORE the
call; memory changed only in `z[0, 32)` and the callee's stack frame. -/
def Post (z x y m mu : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  valueAt s' z 32 = Fv256.Spec.mulModWithReciprocal (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x2e8, (s.regs regSP).toNat),
    ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x30)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x y m mu : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m, mu] (Pre z x y m mu) (Post z x y m mu) :=
  correctness_proof z x y m mu

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`z.MulModWithReciprocal(x, y, m, mu)`) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y m mu : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, m, mu] s ∧ Pre z x y m mu s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x y m mu s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.MulModWithReciprocal
