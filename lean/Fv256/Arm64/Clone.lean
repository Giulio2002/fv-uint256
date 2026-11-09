import Extracted
import Fv256.Spec.Clone
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.Clone

/-!
# arm64: the compiled `(*uint256.Int).Clone` implements `Fv256.Spec.clone`  (`Fv256/Spec/Clone.lean`)

Calling `z.Clone()` (`z` in `X0`) allocates through `runtime.newobject` and returns normally (no fault, no panic): the result in `X0` is a pointer
`ptr` to a FRESH object (`[ptr, ptr+32)` lies inside the runtime-owned ranges `rt`, 16-byte aligned, writable) whose 32 bytes hold
`Fv256.Spec.clone x`, `x` the number at `z` before the call, and memory is unchanged outside `rt` and the stack window. The only assumption about
the runtime is the explicit allocator contract `hnew` (not extracted); see `docs/RUNTIME-CONTRACTS.md` of Janus. The tactic proof is
`Fv256/Proofs/Arm64/Clone.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Clone

/-- Address of `uint256.Int`'s type descriptor, the argument `Clone` passes to `runtime.newobject` (the `ADRP` + `ADD`
pair at `Clone+0x1c`), recomputed from the extracted words. -/
def typeDescAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).Clone" 7)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).Clone" 8) 0

/-- PRECONDITION (machine facts only): the stack-growth check falls through (`GuardOK`) and the stack window
`[SP-4144, SP+24)` (4096 bytes for the runtime plus spill slots) is writable and aligned (`StackOK`), outside the
runtime ranges `rt`; the read-only data (the type descriptor) is loaded; `H` (the runtime's ready-state predicate)
holds for the type descriptor argument. The 32 bytes at `z` are readable, outside `rt` and outside the stack window. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧ Outside (s.sp.toNat - 4144) 4168 rt ∧
  Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
  H [typeDescAddr] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)

/-- POSTCONDITION: the result is a pointer `ptr` (`X0`) to a fresh object: inside `rt`, 16-byte aligned, writable, whose
32 bytes hold `Fv256.Spec.clone` of the number at `z` before the call; memory changed only inside `rt` and the stack
window. -/
def Post (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
  val256 s'.mem ptr = Fv256.Spec.clone (val256 s.mem z.toNat) ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])

set_option maxRecDepth 20000 in
/-- THE CLAIM, under the explicit runtime-contract hypothesis `hnew` (any implementation `impl` of `runtime.newobject` meeting the
allocation contract): every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z] (Pre rt H z) (Post rt z) :=
  correctness_proof impl rt H z hnew

namespace Witness

open Janus.Contracts.IfaceModel

/-- NON-VACUITY: the allocator contract and `Pre` are jointly satisfiable (a toy allocator is linked at the `runtime.newobject`
address, its contract is proved, and a concrete call state meets `Pre`), and that call returns with `Post`, so `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    Pre rt H z s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z s s' :=
  Wit.nonvacuous

end Witness

end Fv256.Arm64.Clone
