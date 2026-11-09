import Extracted
import Fv256.Spec.Bytes
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.Bytes
import Fv256.Proofs.Arm64.BytesBridge

/-!
# arm64: the compiled `(*uint256.Int).Bytes() []byte` implements `Spec.bytes`  (`Fv256/Spec/Bytes.lean`)

`z.Bytes()` (`z` in `X0`) returns normally (no fault, no panic) obeying the ABI. It allocates a fresh 32-byte array (an explicit
runtime contract: `runtime.newobject` returns a 16-aligned, accessible, zeroed block inside the heap ranges `rt`) and returns the
slice of its last `minBytes x` bytes (`X0` = data pointer, `X1` = `X2` = length = `Spec.minBytes x`) whose contents are
`Fv256.Spec.bytes x`, the minimal big-endian encoding of the number `x` at `z` (read before the call); memory changes only inside
the allocator's heap ranges and the callee frame.
The proof is `Fv256/Proofs/Arm64/Bytes.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/BytesBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.Bytes

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4176-byte frame window below `SP` and the 24 bytes above it are writable and aligned; the read-only data is loaded; the frame is outside the heap ranges `rt`; `z` addresses 32 readable bytes outside `rt` and disjoint from the frame; `H` is the allocator-state predicate for the `runtime.newobject` request at the goroutine `g` (`X28`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4176 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4176) 4200 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
  Disjoint z.toNat 32 (s.sp.toNat - 4176) 4200 ∧
  H [intType] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt s.mem)

/-- POSTCONDITION: the returned slice points into a fresh accessible 32-byte block `ptr` inside `rt`, at offset `off` (`0` for an empty slice, else the block's tail `32 - n`), has length and capacity `n = Spec.minBytes x`, and its `n` bytes are `Spec.bytes x` for the number `x` at `z` BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (z : BitVec 64) (s s' : State) : Prop :=
  let v := val256 s.mem z.toNat
  let n := Fv256.Spec.minBytes v
  let off := if n = 0 then 0 else 32 - n
  ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
    (s'.regs 0).toNat = ptr + off ∧ (s'.regs 1).toNat = n ∧ (s'.regs 2).toNat = n ∧
    (List.range n).map (fun i => s'.mem.readLE (ptr + off + i) 1) = Fv256.Spec.bytes v ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4176, s.sp.toNat + 24)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (z : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt z) :=
  Ensures.mono (correctness_proof impl rt H z hnew) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64), NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre rt H z s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z s s' := by
  obtain ⟨impl, rt, H, ret, s, z, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt z s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.Bytes
