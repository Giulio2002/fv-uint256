import Extracted
import Fv256.Spec.MarshalSSZInto
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.MarshalSSZIntoMain
import Fv256.Proofs.Amd64.MarshalSSZIntoBridge

/-!
# amd64: the compiled `(*uint256.Int).MarshalSSZInto(dst []byte) ([]byte, error)` implements `Spec.marshalSSZInto`  (`Fv256/Spec/MarshalSSZInto.lean`)

`z.MarshalSSZInto(dst)` (`z` in `RAX`, the slice `dst` = pointer `dp`, length, capacity in `RBX`, `RCX`, `RDI`) returns normally (no fault, no
panic) obeying the ABI. With `32 ≤ len`: `dst[0, 32)` becomes `Fv256.Spec.marshalSSZInto x` (the 32-byte little-endian encoding of the number
`x` at `z`, read before the call), the result is the slice `dst[32:]` and the error is nil. With `len < 32`: nothing but the callee frame and the
freshly allocated error is written, and the result is `(nil, err)` where `err` is `fmt.Errorf("%w: have %d, want 32 bytes",
ErrBadBufferLength, len)` (modelled, with the live `fmt.Errorf`/`convT64` contracts, by `ErrPre`/`ErrPost` in
`Fv256/Spec/Amd64/MarshalSSZIntoMain.lean`: runtime-level, not part of the readable spec).
The proof is `Fv256/Proofs/Amd64/MarshalSSZInto.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/MarshalSSZIntoBridge.lean`.
-/

open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf

namespace Fv256.Amd64.MarshalSSZInto

/-- PRECONDITION: the stack-growth check falls through; the return-address slot and the 96-byte frame are writable; `len ≤ cap < 2^48` (well-formed slice header); when `32 ≤ len`: `z` addresses 32 readable and `dp` 32 writable bytes, equal-or-disjoint from each other (here disjoint) and from the frame; when `len < 32`: `ErrPre`, the runtime-contract state the error construction needs (live `fmt.Errorf`, `convT64`, the `ErrBadBufferLength` variable, heap invariants). -/
def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
  (32 ≤ len.toNat → Buffer s z 32 false ∧ Buffer s dp 32 true ∧
    (z.toNat + 32 ≤ dp.toNat ∨ dp.toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (dp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat)) ∧
  (len.toNat < 32 → Fv256.Amd64.MarshalSSZIntoMain.ErrPre R Ri H L bud e tp tl z dp len cap s)

/-- POSTCONDITION: with `32 ≤ len` the result is `dst[32:]` (pointer advanced by 32 unless the capacity is exhausted, length `len - 32`, capacity `cap - 32`) with a nil error; the bytes `dst[0, 32)` are `Spec.marshalSSZInto` of the number at `z` BEFORE the call; memory changed only there and in the callee frame. With `len < 32`: `ErrPost` (the wrapped `ErrBadBufferLength` error and its message, `z` and `dst` unchanged). -/
def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (32 ≤ len.toNat →
    s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 3 = len - 32#64 ∧
    s'.regs 1 = cap - 32#64 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
    (List.range 32).map (fun i => s'.mem.readLE (dp.toNat + i) 1) = Fv256.Spec.marshalSSZInto (valueAt s z 32) ∧
    Janus.MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
      ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]) ∧
  (len.toNat < 32 → Fv256.Amd64.MarshalSSZIntoMain.ErrPost R Ri L bud e tp tl z dp len cap s s')

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Amd64.Segment)
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
  Ensures.mono (Fv256.Amd64.MarshalSSZIntoMain.correctness_proof impl R Ri hl H hf hconv L bud e tp tl z dp len cap) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R Ri L bud e tp tl z dp len cap s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (ret : Nat) (s : State) (z dp len cap : BitVec 64), Ri.Laws ∧ ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26 fmtNum 4294967296 ∧ ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧ Pre R Ri H L bud e tp tl z dp len cap s ∧ len.toNat < 32 ∧ (∃ s_c : State, s_c.rip = BitVec.ofNat 64 cAddrC ∧ Fv256.CallSites.ConvT64Site Ri H s_c) ∧ (∃ s_c : State, s_c.rip = BitVec.ofNat 64 cAddrE ∧ Fv256.CallSites.ErrorfLiveSite R cAddrE 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] 138 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R Ri L bud e tp tl z dp len cap s s' := by
  obtain ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, dp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr⟩ := Fv256.Amd64.MarshalSSZIntoMain.Wit.nonvacuous
  exact ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, dp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R Ri L bud e tp tl z dp len cap s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.MarshalSSZInto
