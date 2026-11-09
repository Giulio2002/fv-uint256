import Extracted
import Fv256.Spec.PaddedBytes
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.PaddedBytes
import Fv256.Proofs.Arm64.PaddedBytesBridge

/-!
# arm64: the compiled `(*uint256.Int).PaddedBytes(n int) []byte` implements `Spec.paddedBytes`  (`Fv256/Spec/PaddedBytes.lean`)

`z.PaddedBytes(n)` (`z` in `X0`, `n` in `X1`) returns normally (no fault, no panic) obeying the ABI. It allocates a fresh `n`-byte
slice (explicit runtime contract: `runtime.makeslice` returns a block inside the heap ranges `rt`, as described by the allocator-state
predicate `H`) and fills it with `Fv256.Spec.paddedBytes x n`: the number `x` at `z` (read before the call) as `n` big-endian bytes,
zero-padded in front when `n > 32` and truncated to its low `n` bytes when `n < 32`. The slice is `(X0, X1, X2) = (ptr, n, n)`.
SCOPE: `n ≤ 2^48` (negative `n`, i.e. huge as unsigned, panics in `make` and is excluded by `hn`).
The proof is `Fv256/Proofs/Arm64/PaddedBytes.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/PaddedBytesBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4144-byte frame window below `SP` and the 24 bytes above it are writable and aligned; read-only data loaded; frame outside `rt`; `z` addresses 32 readable bytes outside `rt` and disjoint from the frame; `H` is the allocator-state predicate for the `runtime.makeslice(byte, n, n)` request at the goroutine `g` (`X28`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
  Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
  H [byteType, n.toNat, n.toNat] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem)

/-- POSTCONDITION: the returned slice is `(ptr, n, n)`; for `n > 0` its `n` bytes lie in an accessible block inside `rt` and read as `Spec.paddedBytes` of the number at `z` BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (z n : BitVec 64) (s s' : State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = n.toNat ∧ (s'.regs 2).toNat = n.toNat ∧
  (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
  (List.range n.toNat).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.paddedBytes (val256 s.mem z.toNat) n.toNat ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (z n : BitVec 64)
    (hn : n.toNat ≤ 2 ^ 48)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      (Pre rt H z n) (Post rt z n) :=
  Ensures.mono (correctness_proof impl rt H z n hn hmk) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt z n s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z n : BitVec 64), MakesliceContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, n] s ∧ n.toNat ≤ 2 ^ 48 ∧ Pre rt H z n s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ MakesliceSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z n s s' := by
  obtain ⟨impl, rt, H, ret, s, z, n, h0, h1, h2, h3, h4, h5, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, n, h0, h1, h2, h3, h4, h5, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt z n s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.PaddedBytes
