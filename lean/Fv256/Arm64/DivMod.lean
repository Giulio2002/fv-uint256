import Extracted
import Fv256.Spec.DivMod
import Fv256.Spec.Arm64.DivMod
import Fv256.Arm64.Machine
import Fv256.Proofs.Arm64.DivMod

/-!
# arm64: the compiled `(*uint256.Int).DivMod` implements `Spec.div` and `Spec.mod`  (`Fv256/Spec/DivMod.lean`)

`z.DivMod(x, y, m)` (`X0, X1, X2, X3`) returns normally (no fault, no panic, also for `y = 0`) with `X0 = z`, leaves
`Spec.div x y` (the quotient, `0` when `y = 0`) in `z` and `Spec.mod x y` (the remainder) in the returned second
pointer `X1 = m'`, and writes only `z[0, 32)`, the memory `m'` points to, its own stack frame and the runtime's allocation area.
If `z` and `m` are different objects, `m' = m`; if they are the same object, the Go code allocates a fresh 32-byte object
(`runtime.newobject`) for the remainder and `m'` points into the allocator's range.
The allocator is not part of the compiled library: it is described by the explicit RUNTIME-CONTRACT hypothesis `hnew` of the
theorem (`Janus.Contracts.NewobjectContract`: what `runtime.newobject` does to memory and registers), instantiated with an
allocator state `H`, the allocator's range `rt` and the implementation `impl` of the runtime code.
The proof is `Fv256/Proofs/Arm64/DivMod.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.Arm64.CallSites

namespace Fv256.Arm64.DivMod

/-- PRECONDITION (machine facts plus the runtime state). Stack: the stack-growth check falls through (`GuardOK`), the window
`[SP-4256, SP+40)` (this frame, the allocator's frame and the caller's slots) is usable (`StackOK`) and outside the allocator's
range `rt`. Data: the read-only data of the binary is loaded. Buffers: `z`, `m` writable, `x`, `y` readable, 32 bytes each, none
inside the allocator range `rt` or overlapping the window; `z` is equal to or disjoint from `m` (`x`, `y` may alias anything).
Runtime: the goroutine's `stackguard0` word (at `X28`) is outside the window and `rt`, and the allocator state `H` knows the
`uint256.Int` type descriptor. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64) (s : State) : Prop :=
  GuardOK s 464 ∧ StackOK s 4256 40 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4256) (4256 + 40) rt ∧
  Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m true ∧
  Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
  Janus.Spec.Disjoint z.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Janus.Spec.Disjoint x.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
  Janus.Spec.Disjoint y.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Janus.Spec.Disjoint m.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
  (z = m ∨ Disjoint32 z.toNat m.toNat) ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
  Outside ((s.regs 28).toNat + 16) 8 rt ∧
  H [intType] (s.regs 28).toNat (s.sp.toNat - 160) (rtView rt s.mem)

/-- POSTCONDITION: `X0 = z`; `X1` is a pointer `m'` (equal to `m` unless `z = m`, in which case it is a fresh 16-byte aligned,
writable 32-byte object inside `rt`); the number at `z` is `Spec.div` and the number at `m'` is `Spec.mod`, both of the numbers at `x` and `y` BEFORE the call; memory changed only in `rt`, `z[0, 32)`, `m[0, 32)` and the stack
window. -/
def Post (rt : List (Nat × Nat)) (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  ∃ m' : Nat, (s'.regs 1).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
    (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
    val256 s'.mem z.toNat = Fv256.Spec.div (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
    val256 s'.mem m' = Fv256.Spec.mod (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
    MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
      (s.sp.toNat - 4256, s.sp.toNat + 40)])

/-- THE CLAIM: under the runtime contract `hnew` for `runtime.newobject`, every call meeting `Pre` returns (ABI obeyed) in a
state meeting `Post`. The program is the extraction linked with the runtime implementation `impl`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m] (Pre rt H z x y m) (Post rt z x y m) :=
  correctness_proof impl rt H z x y m hnew

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: every hypothesis (the runtime contract `hnew` included) holds together for a concrete toy allocator at
`runtime.newobject`'s address and a concrete call (distinct `z`, `x`, `y`, `m`), and that call returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, x, y, m] s ∧
    Pre rt H z x y m s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z x y m s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.DivMod
