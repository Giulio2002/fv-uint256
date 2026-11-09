import Extracted
import Fv256.Spec.UnmarshalSSZ
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.UnmarshalSSZMain
import Fv256.Proofs.Arm64.UnmarshalSSZBridge

/-!
# arm64: the compiled `(*uint256.Int).UnmarshalSSZ(buf []byte) error` implements `Spec.unmarshalSSZ`  (`Fv256/Spec/UnmarshalSSZ.lean`)

`z.UnmarshalSSZ(buf)` (`z` in `X0`, the slice `buf` = pointer `bp`, length, capacity in `X1`, `X2`, `X3`) returns normally (no fault, no
panic) obeying the ABI. With `len = 32`: `Fv256.Spec.unmarshalSSZ buf = some v` where `v` is the number now at `z` (the little-endian decoding of
the 32 bytes of `buf`), the error is nil and only `z[0, 32)` and the callee frame are written. With `len ≠ 32`: `z` is unchanged and the
result is `err` wrapping `ErrBadEncodedLength` (`"bad ssz encoded length: have <len>, want 32 bytes"`), modelled with the live
`fmt.Errorf`/`convT64` contracts by `ErrPre`/`ErrPost` in `Fv256/Spec/Arm64/UnmarshalSSZMain.lean` (runtime level, not part of the readable spec).
The proof is `Fv256/Proofs/Arm64/UnmarshalSSZ.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/UnmarshalSSZBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.UnmarshalSSZ

/-- PRECONDITION: the stack-growth check falls through; the 120-byte frame (and 24 bytes above) is writable and aligned; the frame pointer is the caller's (`X29 = SP - 8`); `len ≤ cap < 2^48`; when `len = 32`: `z` addresses 32 writable and `bp` 32 readable bytes, disjoint from each other and from the frame; when `len ≠ 32`: `ErrPre`, the runtime-contract state the error construction needs (live `fmt.Errorf`, `convT64`, the `ErrBadEncodedLength` variable, heap invariants). -/
def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ s.regs 29 = s.sp - 8#64 ∧
  (len.toNat = 32 → Ptr32 s.mem z true ∧ Ptr32 s.mem bp false ∧
    Disjoint z.toNat 32 bp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
    Disjoint bp.toNat 32 (s.sp.toNat - 120) 144) ∧
  (len.toNat ≠ 32 → Fv256.Arm64.UnmarshalSSZMain.ErrPre R Ri H L bud e tp tl z bp len cap s)

/-- POSTCONDITION: with `len = 32` the error is nil (`X0 = X1 = 0`), the number now at `z` is the decoding `Spec.unmarshalSSZ` of the 32 bytes of `buf` BEFORE the call, and memory changed only in `z[0, 32)` and the callee frame. With `len ≠ 32`: `ErrPost` (the wrapped `ErrBadEncodedLength` error and its message, `z` and `buf` unchanged). -/
def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  (len.toNat = 32 →
    s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧
    Fv256.Spec.unmarshalSSZ ((List.range 32).map (fun i => s.mem.readLE (bp.toNat + i) 1)) = some (val256 s'.mem z.toNat) ∧
    MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) ∧
  (len.toNat ≠ 32 → Fv256.Arm64.UnmarshalSSZMain.ErrPost R Ri L bud e tp tl z bp len cap s s')

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
    (z bp len cap : BitVec 64) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp, len, cap]
      (Pre R Ri H L bud e tp tl z bp len cap) (Post R Ri L bud e tp tl z bp len cap) :=
  Ensures.mono (Fv256.Arm64.UnmarshalSSZMain.correctness_proof impl R Ri hl H hf hconv L bud e tp tl z bp len cap) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R Ri L bud e tp tl z bp len cap s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (ret : Nat) (s : State) (z bp len cap : BitVec 64), Ri.Laws ∧ ErrorfLive (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.errorf") 4096 R tErr iErr tInt iWrap 26 fmtNum 4294967296 ∧ ConvT64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.convT64") Ri H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, bp, len, cap] s ∧ Pre R Ri H L bud e tp tl z bp len cap s ∧ len.toNat ≠ 32 ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.convT64") ∧ ConvT64Site Ri H s_c) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.errorf") ∧ ErrorfLiveSite R (Extracted.program.contractAddr "fmt.errorf") 4096 tErr iErr tInt iWrap 26 fmtNum 4294967296 [] 176 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R Ri L bud e tp tl z bp len cap s s' := by
  obtain ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, bp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr⟩ := Fv256.Arm64.UnmarshalSSZMain.Wit.nonvacuous
  exact ⟨impl, R, Ri, H, L, bud, e, tp, tl, ret, s, z, bp, len, cap, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R Ri L bud e tp tl z bp len cap s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.UnmarshalSSZ
