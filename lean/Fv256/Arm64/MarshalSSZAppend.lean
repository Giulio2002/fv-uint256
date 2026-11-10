import Extracted
import Fv256.Spec.MarshalSSZAppend
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.MarshalSSZAppendMain
import Fv256.Proofs.Arm64.MarshalSSZAppendBridge

/-!
# arm64: the compiled `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` implements `Spec.marshalSSZAppend`  (`Fv256/Spec/MarshalSSZAppend.lean`)

`z.MarshalSSZAppend(dst)` (`z` in `X0`, the slice `dst` = pointer `dp`, length `len`, capacity `cap` in `X1`, `X2`, `X3`) returns normally (no
fault, no panic) obeying the ABI with the slice `(X0, X1, X2)` of length `len + 32` and a nil error (`X3 = X4 = 0`). The first `len` elements
are `dst`'s, and the 32 elements after them are `Fv256.Spec.marshalSSZAppend x` (the little-endian encoding of the number `x` at `z`, read before the
call). If `len + 32 ≤ cap` the result shares `dst`'s array (same pointer and capacity, only `dst[len, len + 32)` is written); otherwise
`runtime.growslice` allocates a larger array (explicit runtime contract `hgs`: the live growslice model with its heap invariant `R.inv`) and the old
elements are copied. SCOPE: well-formed slice and the live-runtime state described in `Pre`.
The proof is `Fv256/Proofs/Arm64/MarshalSSZAppend.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/MarshalSSZAppendBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa Fv256.Arm64.MarshalSSZAppendG
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZAppend

/-- PRECONDITION (machine facts plus the live-runtime state the `growslice` contract needs): see the amd64 claim; here the frame is `[SP-4232, SP+40)` with the frame pointer the caller's, and the goroutine is `X28`. -/
def Pre (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 4224 ∧ StackOK s 4232 40 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
  Disjoint z.toNat 32 (s.sp.toNat - 4232) 4272 ∧
  Outside (s.sp.toNat - 4232) 4272 R.rt ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4232) 4272 ∧
  Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
  Apart ((s.regs 28).toNat + 16) 8 dp.toNat cap.toNat ∧
  R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
  (InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt) ∧
  Apart z.toNat 32 dp.toNat cap.toNat ∧
  len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ dp.toNat + cap.toNat ≤ 2 ^ 48 ∧
  Apart dp.toNat cap.toNat (s.sp.toNat - 4232) 4272 ∧
  Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
  (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
    (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
  (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
  4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat

/-- POSTCONDITION: the result is `(ptr, len + 32, cap')` with a nil error; the 32 bytes after the old `len` are `Spec.marshalSSZAppend` of the number at `z` BEFORE the call and the old prefix is kept byte for byte; with room (`len + 32 ≤ cap`) the pointer and capacity are unchanged, the runtime invariant is preserved and only `dst[len, len + 32)` and the callee frame are written; without room the new array lies inside the runtime ranges, is a live object of some new runtime state, and memory changed only inside the runtime ranges, the callee frame and `dst`'s array. -/
def Post (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 1).toNat = len.toNat + 32 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧ len.toNat + 32 ≤ (s'.regs 2).toNat ∧
  (List.range 32).map (fun i => s'.mem.readLE ((s'.regs 0).toNat + len.toNat + i) 1) = Fv256.Spec.marshalSSZAppend (val256 s.mem z.toNat) ∧
  (∀ i, i < len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp.toNat + i)) ∧
  (len.toNat + 32 ≤ cap.toNat → (s'.regs 0).toNat = dp.toNat ∧ (s'.regs 2).toNat = cap.toNat ∧
    R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
    MemFrame s.mem s'.mem [(dp.toNat + len.toNat, dp.toNat + len.toNat + 32), (s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
  (cap.toNat < len.toNat + 32 → InRanges (s'.regs 0).toNat (s'.regs 2).toNat R.rt ∧
    (∃ b' L', R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧ InRanges (s'.regs 0).toNat (s'.regs 2).toNat L') ∧
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40), (dp.toNat, dp.toNat + cap.toNat)]))

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (R : RtInv)
    (b : Nat)
    (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (Pre R b L z dp len cap) (Post R b L z dp len cap) :=
  Ensures.mono (Fv256.Arm64.MarshalSSZAppendMain.correctness_proof impl R b L z dp len cap hgs) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R b L z dp len cap s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub
open Janus.Contracts.PoolSat (toyInv_init_tys)

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (ret : Nat) (s : State), RtLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R b L z dp len cap s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z dp len cap s s' := by
  obtain ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr⟩ := Fv256.Arm64.MarshalSSZAppendMain.Wit.nonvacuous
  exact ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R b L z dp len cap s s').1 hq.2⟩⟩

end Witness

namespace Grow.Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub
open Janus.Contracts.PoolSat (toyInv_init_tys)

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64) (ret : Nat) (s : State), RtLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R b L z dp len cap s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R b L z dp len cap s s' := by
  obtain ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr⟩ := Fv256.Arm64.MarshalSSZAppendMain.Grow.Wit.nonvacuous
  exact ⟨impl, R, b, L, z, dp, len, cap, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R b L z dp len cap s s').1 hq.2⟩⟩

end Grow.Witness

end Fv256.Arm64.MarshalSSZAppend
