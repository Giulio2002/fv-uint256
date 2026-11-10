import Extracted
import Fv256.Spec.DivMod
import Fv256.Spec.Amd64.DivMod
import Fv256.Amd64.Machine
import Fv256.Proofs.Amd64.DivMod

/-!
# amd64: the compiled `(*uint256.Int).DivMod` implements `Spec.div` and `Spec.mod`  (`Fv256/Spec/DivMod.lean`)

`z.DivMod(x, y, m)` (`RAX, RBX, RCX, RDI`) returns normally (no fault, no panic, also for `y = 0`) with `RAX = z`, leaves
`Spec.div x y` (the quotient, `0` when `y = 0`) in `z` and `Spec.mod x y` (the remainder) in the returned second
pointer `RBX = m'`, and writes only `z[0, 32)`, the memory `m'` points to, its own stack window and the runtime's allocation area.
If `z` and `m` are different objects, `m' = m`; if they are the same object, the Go code allocates a fresh 32-byte object
(`runtime.newobject`) for the remainder and `m'` points into the allocator's range.
The allocator is not part of the compiled library: it is described by the explicit RUNTIME-CONTRACT hypothesis `hnew` of the
theorem (`Janus.Contracts.NewobjectContract64`: what `runtime.newobject` does to memory and registers), instantiated with an
allocator state `H`, the allocator's range `rt` and the implementation `impl` of the runtime code.
The proof is `Fv256/Proofs/Amd64/DivMod.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Fv256.CallSites

namespace Fv256.Amd64.DivMod

/-- PRECONDITION (machine facts plus the runtime state). Stack: the stack-growth check falls through (`StackGuardOK`), the window
`[RSP-4256, RSP+0x28)` (this frame, the allocator's frame and the caller's spill slot) is writable, `RSP` is 8-byte aligned and
the window is outside the allocator's range `rt`. Data: the read-only data of the binary is loaded. Buffers: `z`, `m` writable,
`x`, `y` readable, 32 bytes each, none inside the allocator range `rt` or overlapping the window; `z` is equal to or disjoint
from `m` (`x`, `y` may alias anything). Runtime: the goroutine's `stackguard0` word (`R14`) is outside the window and
`rt`, and the allocator state `H` knows the `uint256.Int` type descriptor. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x198 ∧ StackWritable s 4256 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
  Janus.Outside ((s.regs 4).toNat - 4256) (4256 + 0x28) rt ∧ (s.regs 4).toNat % 8 = 0 ∧
  Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 true ∧
  Janus.Outside z.toNat 32 rt ∧ Janus.Outside x.toNat 32 rt ∧ Janus.Outside y.toNat 32 rt ∧ Janus.Outside m.toNat 32 rt ∧
  Fv256.Amd64.Outside z 32 ((s.regs 4).toNat - 4256) ((s.regs 4).toNat + 0x28) ∧
  Fv256.Amd64.Outside x 32 ((s.regs 4).toNat - 4256) ((s.regs 4).toNat + 0x28) ∧
  Fv256.Amd64.Outside y 32 ((s.regs 4).toNat - 4256) ((s.regs 4).toNat + 0x28) ∧
  Fv256.Amd64.Outside m 32 ((s.regs 4).toNat - 4256) ((s.regs 4).toNat + 0x28) ∧
  Fv256.Amd64.Alias32 z m ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16) ∧
  Janus.Outside ((s.regs 14).toNat + 16) 8 rt ∧
  H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 0xa0) (rtView rt s.mem)

/-- POSTCONDITION: `RAX = z`; `RBX` is a pointer `m'` (equal to `m` unless `z = m`, in which case it is a fresh 16-byte aligned,
writable 32-byte object inside `rt`); the number at `z` is `Spec.div` and the number at `m'` is `Spec.mod`, both of the numbers at `x` and `y` BEFORE the call; memory changed only in `rt`, `z[0, 32)`, `m[0, 32)` and the stack
window. -/
def Post (rt : List (Nat × Nat)) (z x y m : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = z ∧
  ∃ m' : Nat, (s'.regs 3).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
    (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
    valueAt s' z 32 = Fv256.Spec.div (valueAt s x 32) (valueAt s y 32) ∧
    s'.mem.readLE m' 32 = Fv256.Spec.mod (valueAt s x 32) (valueAt s y 32) ∧
    MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
      ((s.regs 4).toNat - 4256, (s.regs 4).toNat + 0x28)])

/-- THE CLAIM: under the runtime contract `hnew` for `runtime.newobject`, every call meeting `Pre` returns (ABI obeyed) in a
state meeting `Post`. The program is the extraction linked with the runtime implementation `impl`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m] (Pre rt H z x y m) (Post rt z x y m) :=
  correctness_proof impl rt H z x y m hnew

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: every hypothesis (the runtime contract `hnew` included) holds together for a concrete toy allocator at
`runtime.newobject`'s address and a concrete call (distinct `z`, `x`, `y`, `m`), and that call returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (ret : Nat) (s : Amd64.State),
    NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectSite H rt 4096 s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, x, y, m] s ∧
    Pre rt H z x y m s ∧
    Returns ((Extracted.program.link impl).withExit ret) s (fun s' => ABIReturn s s' ∧ Post rt z x y m s s') :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.DivMod
