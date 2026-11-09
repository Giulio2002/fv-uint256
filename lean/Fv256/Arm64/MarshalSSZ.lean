import Extracted
import Fv256.Spec.MarshalSSZ
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.MarshalSSZ
import Fv256.Proofs.Arm64.MarshalSSZBridge

/-!
# arm64: the compiled `(*uint256.Int).MarshalSSZ() ([]byte, error)` implements `Spec.marshalSSZ`  (`Fv256/Spec/MarshalSSZ.lean`)

`z.MarshalSSZ()` (`z` in `X0`) returns normally (no fault, no panic) obeying the ABI. It allocates a fresh 32-byte slice (explicit
runtime contract: `runtime.makeslice(byte, 0, 32)` returns a block inside the heap ranges `rt`) whose bytes are
`Fv256.Spec.marshalSSZ x`, the 32-byte little-endian SSZ encoding of the number `x` at `z` (read before the call). The results are
the slice `(X0, X1, X2) = (ptr, 32, 32)` and a nil `error` (`X3 = X4 = 0`).
The proof is `Fv256/Proofs/Arm64/MarshalSSZ.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/MarshalSSZBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.MarshalSSZ

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4144-byte frame window below `SP` and the 24 bytes above it are writable and aligned; read-only data loaded; frame outside `rt`; `z` addresses 32 readable bytes outside `rt` and disjoint from the frame; `H` is the allocator-state predicate for the `runtime.makeslice(byte, 0, 32)` request at the goroutine `g` (`X28`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
  Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
  H [byteType, 0, 32] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)

/-- POSTCONDITION: the returned slice is `(ptr, 32, 32)` with a nil error; its 32 bytes lie in an accessible block inside `rt` and are `Spec.marshalSSZ` of the number at `z` BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 32 ∧ (s'.regs 2).toNat = 32 ∧
  s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
  (List.range 32).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.marshalSSZ (val256 s.mem z.toNat) ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (z : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt z) :=
  Ensures.mono (correctness_proof impl rt H z hmk) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State), MakesliceContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre rt H z s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ MakesliceSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z s s' := by
  obtain ⟨impl, rt, H, z, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, z, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt z s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.MarshalSSZ
