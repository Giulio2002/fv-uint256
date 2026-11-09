import Extracted
import Fv256.Spec.MarshalSSZInto
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.MarshalSSZIntoMain
import Fv256.Proofs.Arm64.MarshalSSZIntoBridge

/-!
# arm64: the compiled `(*uint256.Int).MarshalSSZInto(dst []byte) ([]byte, error)` implements `Spec.marshalSSZInto`  (`Fv256/Spec/MarshalSSZInto.lean`)

`z.MarshalSSZInto(dst)` (`z` in `X0`, the slice `dst` = pointer `dp`, length, capacity in `X1`, `X2`, `X3`) returns normally (no fault, no
panic) obeying the ABI. With `32 ≤ len`: `dst[0, 32)` becomes `Fv256.Spec.marshalSSZInto x` (the 32-byte little-endian encoding of the number
`x` at `z`, read before the call), the result is the slice `dst[32:]` and the error is nil. With `len < 32`: nothing but the callee frame and the
freshly allocated error is written, and the result is `(nil, err)` where `err` is `fmt.Errorf("%w: have %d, want 32 bytes",
ErrBadBufferLength, len)` (modelled, with the live `fmt.Errorf`/`convT64` contracts, by `ErrPre`/`ErrPost` in
`Fv256/Spec/Arm64/MarshalSSZIntoMain.lean`: runtime-level, not part of the readable spec).
The proof is `Fv256/Proofs/Arm64/MarshalSSZInto.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/MarshalSSZIntoBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZInto

/-- PRECONDITION: the stack-growth check falls through; the 120-byte frame (and 24 bytes above) is writable and aligned; the frame pointer is the caller's (`X29 = SP - 8`); `len ≤ cap < 2^48`; when `32 ≤ len`: `z` addresses 32 readable and `dp` 32 writable bytes, disjoint from each other and from the frame; when `len < 32`: `ErrPre`, the runtime-contract state the error construction needs (live `fmt.Errorf`, `convT64`, the `ErrBadBufferLength` variable, heap invariants). -/
def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ s.regs 29 = s.sp - 8#64 ∧
  (32 ≤ len.toNat → Ptr32 s.mem z false ∧ Ptr32 s.mem dp true ∧
    Disjoint z.toNat 32 dp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
    Disjoint dp.toNat 32 (s.sp.toNat - 120) 144) ∧
  (len.toNat < 32 → Fv256.Arm64.MarshalSSZIntoMain.ErrPre R Ri H L bud e tp tl z dp len cap s)

/-- POSTCONDITION: with `32 ≤ len` the result is `dst[32:]` (pointer advanced by 32 unless the capacity is exhausted, length `len - 32`, capacity `cap - 32`) with a nil error; the bytes `dst[0, 32)` are `Spec.marshalSSZInto` of the number at `z` BEFORE the call; memory changed only there and in the callee frame. With `len < 32`: `ErrPost` (the wrapped `ErrBadBufferLength` error and its message, `z` and `dst` unchanged). -/
def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (32 ≤ len.toNat →
    s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 1 = len - 32#64 ∧
    s'.regs 2 = cap - 32#64 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
    (List.range 32).map (fun i => s'.mem.readLE (dp.toNat + i) 1) = Fv256.Spec.marshalSSZInto (val256 s.mem z.toNat) ∧
    MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) ∧
  (len.toNat < 32 → Fv256.Arm64.MarshalSSZIntoMain.ErrPost R Ri L bud e tp tl z dp len cap s s')

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (R : RtInv)
    (Ri : IfaceModel)
    (hl : Ri.Laws)
    (H : RtReady)
    (hf : ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R
      tErr iErr tInt iWrap 26 fmtNum 4294967296)
    (hconv : ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H)
    (L : List (Nat × Nat))
    (bud e tp tl : Nat)
    (z dp len cap : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (Pre R Ri H L bud e tp tl z dp len cap) (Post R Ri L bud e tp tl z dp len cap) :=
  Ensures.mono (Fv256.Arm64.MarshalSSZIntoMain.correctness_proof impl R Ri hl H hf hconv L bud e tp tl z dp len cap) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R Ri L bud e tp tl z dp len cap s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (ret : Nat) (s : State) (z dp len cap : BitVec 64), Ri.Laws ∧ ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26 fmtNum 4294967296 ∧ ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R Ri H L bud e tp tl z dp len cap s ∧ len.toNat < 32 ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.convT64") ∧ ConvT64Site Ri H s_c) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.errorf") ∧ ErrorfLiveSite R (Extracted.program.contractAddr "fmt.errorf") 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] 138 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R Ri L bud e tp tl z dp len cap s s' := by
  obtain ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, dp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr⟩ := Fv256.Arm64.MarshalSSZIntoMain.Wit.nonvacuous
  exact ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, dp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R Ri L bud e tp tl z dp len cap s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.MarshalSSZInto
