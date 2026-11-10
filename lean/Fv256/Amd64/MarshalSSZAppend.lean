import Extracted
import Fv256.Spec.MarshalSSZAppend
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.MarshalSSZAppendMain
import Fv256.Proofs.Amd64.MarshalSSZAppendBridge

/-!
# amd64: the compiled `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` implements `Spec.marshalSSZAppend`  (`Fv256/Spec/MarshalSSZAppend.lean`)

`z.MarshalSSZAppend(dst)` (`z` in `RAX`, the slice `dst` = pointer `dp`, length `len`, capacity `cap` in `RBX`, `RCX`, `RDI`) returns normally (no
fault, no panic) obeying the ABI with the slice `(RAX, RCX, RBX)` of length `len + 32` and a nil error (`RDI = RSI = 0`). The first `len` elements
are `dst`'s, and the 32 elements after them are `Fv256.Spec.marshalSSZAppend x` (the little-endian encoding of the number `x` at `z`, read before the
call). If `len + 32 ≤ cap` the result shares `dst`'s array (same pointer and capacity, only `dst[len, len + 32)` is written); otherwise
`runtime.growslice` allocates a larger array (explicit runtime contract `hgs`: the live growslice model with its heap invariant `R.inv`) and the old
elements are copied. SCOPE: well-formed slice (`len ≤ cap < 2^40`, `dp + cap ≤ 2^48`) and the live-runtime state described in `Pre`.
The proof is `Fv256/Proofs/Amd64/MarshalSSZAppend.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/MarshalSSZAppendBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)
open Fv256.Msa Fv256.Amd64.Msa

namespace Fv256.Amd64.MarshalSSZAppend

/-- PRECONDITION (machine facts plus the live-runtime state the `growslice` contract needs): stack-growth check falls through; the 4208-byte frame (and 24 bytes above) is writable; `RSP` 8-aligned; read-only data loaded; `z` addresses 32 readable bytes apart from the frame, the slice array and the runtime ranges; the runtime invariant `R.inv` holds for the live set `L`; the slice header is well formed (`len ≤ cap < 2^40`, `dp + cap ≤ 2^48`); the type descriptor of `uint8` is intact and apart from the frame and the array; in the no-growth case (`len + 8 ≤ cap`, the proof's condition) the array is writable and live or outside the runtime ranges, in the growth case its prefix is readable; the growslice budget `Kc` fits the runtime budget `b`; `Msa.Ready` (the allocator can serve the request). -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4208 ∧ StackWritable s 4208 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
  Extracted.program.DataLoaded s.mem ∧ Buffer s z 32 false ∧
  Apart z.toNat 32 ((s.regs 4).toNat - 4208) 4232 ∧
  Outside ((s.regs 4).toNat - 4208) 4232 R.rt ∧
  Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4208) 4232 ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
  Apart ((s.regs 14).toNat + 16) 8 dp.toNat cap.toNat ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]) ∧
  (InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt) ∧
  Apart z.toNat 32 dp.toNat cap.toNat ∧
  len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ dp.toNat + cap.toNat ≤ 2 ^ 48 ∧
  Apart dp.toNat cap.toNat ((s.regs 4).toNat - 4208) 4232 ∧
  Apart u8T 16 ((s.regs 4).toNat - 4208) 4232 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
  (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
    (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
  (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
  4 * Kc len.toNat ≤ b ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 (len.toNat + 8) cap.toNat

/-- POSTCONDITION: the result is `(ptr, len + 32, cap')` with a nil error; the 32 bytes after the old `len` are `Spec.marshalSSZAppend` of the number at `z` BEFORE the call and the old prefix is kept byte for byte; with room (`len + 32 ≤ cap`) the pointer and capacity are unchanged, the runtime invariant is preserved and only `dst[len, len + 32)` and the callee frame are written; without room the new array lies inside the runtime ranges, is a live object of some new runtime state, and memory changed only inside the runtime ranges, the callee frame and `dst`'s array. -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 3).toNat = len.toNat + 32 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧ len.toNat + 32 ≤ (s'.regs 1).toNat ∧
  (List.range 32).map (fun i => s'.mem.readLE ((s'.regs 0).toNat + len.toNat + i) 1) = Fv256.Spec.marshalSSZAppend (valueAt s z 32) ∧
  (∀ i, i < len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp.toNat + i)) ∧
  (len.toNat + 32 ≤ cap.toNat → (s'.regs 0).toNat = dp.toNat ∧ (s'.regs 1).toNat = cap.toNat ∧
    R.inv b L (s.regs 14).toNat (view R.rt L s'.mem) ∧
    MemFrame s.mem s'.mem [(dp.toNat + len.toNat, dp.toNat + len.toNat + 32), ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]) ∧
  (cap.toNat < len.toNat + 32 → InRanges (s'.regs 0).toNat (s'.regs 1).toNat R.rt ∧
    (∃ b' L', R.inv b' L' (s.regs 14).toNat (view R.rt L' s'.mem) ∧ InRanges (s'.regs 0).toNat (s'.regs 1).toNat L') ∧
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp.toNat + len.toNat, dp.toNat + cap.toNat)]))

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Amd64.Segment)
    (R : RtInv)
    (b : Nat)
    (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (Pre R b L z dp len cap) (Post R b L z dp len cap) :=
  Ensures.mono (Fv256.Amd64.MarshalSSZAppendMain.correctness_proof impl R b L z dp len cap hgs) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R b L z dp len cap s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.PoolSat (toyInv_init_tys)

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (ret : Nat) (s : State), RtLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R b L z dp len cap s ∧ (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z dp len cap s s' := by
  obtain ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr⟩ := Fv256.Amd64.MarshalSSZAppendMain.Wit.nonvacuous
  exact ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R b L z dp len cap s s').1 hq.2⟩⟩

end Witness

namespace Grow.Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Janus.Contracts.PoolSat (toyInv_init_tys)

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (ret : Nat) (s : State), RtLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R b L z dp len cap s ∧ (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z dp len cap s s' := by
  obtain ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr⟩ := Fv256.Amd64.MarshalSSZAppendMain.Grow.Wit.nonvacuous
  exact ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R b L z dp len cap s s').1 hq.2⟩⟩

end Grow.Witness

end Fv256.Amd64.MarshalSSZAppend
