import Extracted
import Fv256.Spec.Float64
import Fv256.Amd64.Machine
import Fv256.Proofs.Common.Float64Bridge
import Fv256.Proofs.Amd64.Float64

/-!
# amd64: the compiled `(*uint256.Int).Float64` implements `Fv256.Spec.float64Bits`  (`Fv256/Spec/Float64.lean`)

Calling `x.Float64()` with `x` in `RAX` returns normally (no fault, no panic) with the 64-bit pattern of the `float64` nearest to the number at `x`
(IEEE 754 round to nearest, ties to even) in the low 64 bits of `X0`, and writes only its own stack window.
The program is analysed under the default Go floating-point mode (`GoMXCSR`).
The tactic proof is `Fv256/Proofs/Amd64/Float64.lean`; Janus checks that the statement is about the compiled code.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP Fv256.Amd64

namespace Fv256.Amd64.Float64

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`StackGuardOK`); the window `[RSP-80, RSP+8)` is writable; `x` is a readable 32-byte buffer not
overlapping the window; the SSE control/status register has Go's default value (`GoMXCSR`: round to nearest, exceptions masked). -/
def Pre (x : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
  (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s

/-- POSTCONDITION: the low 64 bits of `X0` are `Spec.float64Bits` of the number at `x` (read BEFORE the call); memory changed only in the stack window
`[RSP-80, RSP+8)`. -/
def Post (x : BitVec 64) (s s' : State) : Prop :=
  (s'.xmm 0).toNat % 2 ^ 64 = Fv256.Spec.float64Bits (valueAt s x 32) ∧
  MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x] (Pre x) (Post x) :=
  (correctness_proof x).mono (fun _ h => h) fun s _ _ h =>
    ⟨h.1.trans (Fv256.Float64Bridge.float64Bits_eq_mem s.mem x.toNat).symm, h.2⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (`x.Float64()` on a zero number) satisfies `Pre` and its call returns with `Post`, so `Pre` is not
unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧ Pre x s ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post x s s' :=
  by
    obtain ⟨ret, s, x, hr, hc, hp, hret⟩ := Wit.nonvacuous
    exact ⟨ret, s, x, hr, hc, hp, hret.mono fun s' h =>
      ⟨h.1, h.2.1.trans (Fv256.Float64Bridge.float64Bits_eq_mem s.mem x.toNat).symm, h.2.2⟩⟩

end Witness

end Fv256.Amd64.Float64
