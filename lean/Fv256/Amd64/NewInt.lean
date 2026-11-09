import Extracted
import Fv256.Spec.NewInt
import Fv256.Proofs.Amd64.NewInt

/-!
# amd64: the compiled `uint256.NewInt` implements `Fv256.Spec.newInt`  (`Fv256/Spec/NewInt.lean`)

Calling `uint256.NewInt(val)` (`val` in `RAX`) allocates through `runtime.newobject` and returns normally (no fault, no panic): the result in `RAX` is a pointer
`ptr` to a FRESH object (`[ptr, ptr+32)` lies inside the runtime-owned ranges `rt`, 16-byte aligned, writable) whose 32 bytes hold
`Fv256.Spec.newInt val`, and memory is unchanged outside `rt` and the stack window. The only assumption about
the runtime is the explicit allocator contract `hnew` (not extracted); see `docs/RUNTIME-CONTRACTS.md` of Janus. The tactic proof is
`Fv256/Proofs/Amd64/NewInt.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.NewInt

/-- Address of `uint256.Int`'s type descriptor (the `LEA` before the call to `runtime.newobject` loads it): the
extraction's only data object. -/
def typeDescAddr : Nat := dataBase Extracted.program 0

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`StackGuardOK`), the stack window
`[RSP-4128, RSP+24)` is writable (`StackWritable`) and the stack pointer is 8-byte aligned, outside the runtime ranges
`rt`; the read-only data (the type descriptor) is loaded; `H` (the runtime's ready-state predicate) holds for the type
descriptor argument. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (s : Amd64.State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
  H [typeDescAddr] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem)

/-- POSTCONDITION: the result is a pointer `ptr` (`RAX`) to a fresh object: inside `rt`, 16-byte aligned, writable, whose
32 bytes hold `Fv256.Spec.newInt val`; memory changed only inside `rt` and the stack window. -/
def Post (rt : List (Nat × Nat)) (val : BitVec 64) (s s' : Amd64.State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
  s'.mem.readLE ptr 32 = Fv256.Spec.newInt val.toNat ∧
  MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])

set_option maxRecDepth 20000 in
/-- THE CLAIM, under the explicit runtime-contract hypothesis `hnew` (any implementation `impl` of `runtime.newobject` meeting the
allocation contract): every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (val : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [val] (Pre rt H) (Post rt val) :=
  correctness_proof impl rt H val hnew

namespace Witness

open Janus.Contracts.IfaceModel

/-- NON-VACUITY: the allocator contract and `Pre` are jointly satisfiable (a toy allocator is linked at the `runtime.newobject`
address, its contract is proved, and a concrete call state meets `Pre`), and that call returns with `Post`, so `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (val : BitVec 64),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectSite H rt 4096 s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [val] s ∧
    Pre rt H s ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt val s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Amd64.NewInt
