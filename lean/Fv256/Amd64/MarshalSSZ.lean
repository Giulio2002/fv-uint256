import Extracted
import Fv256.Spec.MarshalSSZ
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.MarshalSSZ
import Fv256.Proofs.Amd64.MarshalSSZBridge

/-!
# amd64: the compiled `(*uint256.Int).MarshalSSZ() ([]byte, error)` implements `Spec.marshalSSZ`  (`Fv256/Spec/MarshalSSZ.lean`)

`z.MarshalSSZ()` (`z` in `RAX`) returns normally (no fault, no panic) obeying the ABI. It allocates a fresh 32-byte slice (explicit
runtime contract: `runtime.makeslice(byte, 0, 32)` returns a block inside the heap ranges `rt`) whose bytes are
`Fv256.Spec.marshalSSZ x`, the 32-byte little-endian SSZ encoding of the number `x` at `z` (read before the call). The results are
the slice `(RAX, RBX, RCX) = (ptr, 32, 32)` and a nil `error` (`RDI = RSI = 0`).
The proof is `Fv256/Proofs/Amd64/MarshalSSZ.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/MarshalSSZBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.MarshalSSZ

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4136-byte frame window below `RSP` and the 24 bytes above it are writable; read-only data loaded; frame outside `rt`; `RSP` 8-aligned; `z` addresses 32 readable bytes outside `rt` and the frame; `H` is the allocator-state predicate for the `runtime.makeslice(byte, 0, 32)` request at the goroutine `g` (`R14`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
  Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
  H [byteType, 0, 32] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem)

/-- POSTCONDITION: the returned slice is `(ptr, 32, 32)` with a nil error; its 32 bytes lie in an accessible block inside `rt` and are `Spec.marshalSSZ` of the number at `z` BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 32 ∧ (s'.regs 1).toNat = 32 ∧
  s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ InRanges ptr 32 rt ∧ s'.mem.accessible ptr 32 true = true ∧
  (List.range 32).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.marshalSSZ (valueAt s z 32) ∧
  MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (z : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt z) :=
  Ensures.mono (correctness_proof impl rt H z hmk) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State), MakesliceContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre rt H z s ∧ (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ Fv256.CallSites.MakesliceSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z s s' := by
  obtain ⟨impl, rt, H, z, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, z, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt z s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.MarshalSSZ
