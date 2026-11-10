import Extracted
import Fv256.Spec.PaddedBytes
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.PaddedBytes
import Fv256.Proofs.Amd64.PaddedBytesBridge

/-!
# amd64: the compiled `(*uint256.Int).PaddedBytes(n int) []byte` implements `Spec.paddedBytes`  (`Fv256/Spec/PaddedBytes.lean`)

`z.PaddedBytes(n)` (`z` in `RAX`, `n` in `RBX`) returns normally (no fault, no panic) obeying the ABI. It allocates a fresh `n`-byte
slice (explicit runtime contract: `runtime.makeslice` returns a block inside the heap ranges `rt`, as described by the allocator-state
predicate `H`) and fills it with `Fv256.Spec.paddedBytes x n`: the number `x` at `z` (read before the call) as `n` big-endian bytes,
zero-padded in front when `n > 32` and truncated to its low `n` bytes when `n < 32`. The slice is `(RAX, RBX, RCX) = (ptr, n, n)`.
SCOPE: `n ≤ 2^48` (negative `n`, i.e. huge as unsigned, panics in `make` and is excluded by `hn`).
The proof is `Fv256/Proofs/Amd64/PaddedBytes.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/PaddedBytesBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4136-byte frame window below `RSP` and the 24 bytes above it are writable; read-only data loaded; frame outside `rt`; `RSP` 8-aligned; `z` addresses 32 readable bytes outside `rt` and the frame; `H` is the allocator-state predicate for the `runtime.makeslice(byte, n, n)` request at the goroutine `g` (`R14`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z n : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
  Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
  H [byteType, n.toNat, n.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem)

/-- POSTCONDITION: the returned slice is `(ptr, n, n)`; for `n > 0` its `n` bytes lie in an accessible block inside `rt` and read as `Spec.paddedBytes` of the number at `z` BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (z n : BitVec 64) (s s' : State) : Prop :=
  ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = n.toNat ∧ (s'.regs 1).toNat = n.toNat ∧
  (0 < n.toNat → InRanges ptr n.toNat rt ∧ s'.mem.accessible ptr n.toNat true = true) ∧
  (List.range n.toNat).map (fun i => s'.mem.readLE (ptr + i) 1) = Fv256.Spec.paddedBytes (valueAt s z 32) n.toNat ∧
  MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (z n : BitVec 64)
    (hn : n.toNat ≤ 2 ^ 48)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, n]
      (Pre rt H z n) (Post rt z n) :=
  Ensures.mono (correctness_proof impl rt H z n hn hmk) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt z n s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z n : BitVec 64), MakesliceContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, n] s ∧ n.toNat ≤ 2 ^ 48 ∧ Pre rt H z n s ∧ (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.makeslice") ∧ Fv256.CallSites.MakesliceSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt z n s s' := by
  obtain ⟨impl, rt, H, ret, s, z, n, h0, h1, h2, h3, h4, h5, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, n, h0, h1, h2, h3, h4, h5, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt z n s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.PaddedBytes
