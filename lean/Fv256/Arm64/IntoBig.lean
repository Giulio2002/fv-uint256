import Extracted
import Fv256.Spec.IntoBig
import Fv256.Spec.BigIntAt
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.IntoBig
import Fv256.Proofs.Arm64.BigOutBridge

/-!
# arm64: the compiled `(*uint256.Int).IntoBig(b **big.Int)` implements `Spec.intoBig`  (`Fv256/Spec/IntoBig.lean`)

`z.IntoBig(b)` (`z`, `b` in `X0`, `X1`) returns normally (no fault, no panic) obeying the ABI. For a nil `z` it stores nil in `*b`. Otherwise it
stores in `*b` a pointer `P` to a well-formed `big.Int` of integer value `Fv256.Spec.intoBig x` (the number `x` at `z`, read before the call),
reusing the `big.Int` and the limb array `*b` already points to when they exist (and the array has capacity for four limbs) and allocating
otherwise (explicit runtime contracts `hnew`, `hwb1`, `hwb2`: live models of `runtime.newobject` and `runtime.gcWriteBarrier1/2`).
The proof is `Fv256/Proofs/Arm64/IntoBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/IntoBigBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.IntoBig

/-- PRECONDITION: `Pre` and `PreX` of `Spec/Arm64/IntoBigDefs.lean` (kept there because the generated `TB` modules of `ToBig` share them): the stack frame and live-runtime state the allocator and write-barrier contracts need (see `ToBig`), `bp` addresses the 8 writable bytes of `*b` outside the runtime ranges, when `z` is non-nil it addresses 32 readable bytes, and the existing `big.Int` (if `*b` is non-nil) and its limb array (if its capacity is at least four) are writable and pairwise disjoint from `bp`, `z` and the frame; plus the separation of the goroutine slot. -/
def Claim.Pre (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  Fv256.Arm64.IntoBig.Pre R b z bp s ∧ Fv256.Arm64.IntoBig.PreX z bp s

/-- POSTCONDITION: for a nil `z` the slot `*b` becomes nil; otherwise `*b` points to a well-formed `big.Int` of integer value `Spec.intoBig` of the number at `z` BEFORE the call; memory changed only inside the runtime ranges, the callee frame, the slot `*b`, and the old `big.Int` and limb array (and only the frame, the slot if `*b` was nil). -/
def Claim.Post (R : RtInv) (z bp : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, Fv256.Spec.BigIntSlot s'.mem bp.toNat P (Fv256.Spec.intoBig (val256 s.mem z.toNat))) ∧
  MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
    (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (R : RtInv)
    (b : Nat)
    (z bp : BitVec 64)
    (hnew : NewobjectLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, bp]
      (Claim.Pre R b z bp) (Claim.Post R z bp) :=
  Ensures.mono (correctness_proof impl R b z bp hnew hwb1 hwb2) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R z bp s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (z bp : BitVec 64) (ret : Nat) (s : State), NewobjectLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧ WbLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧ WbLiveContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, bp] s ∧ Claim.Pre R b z bp s ∧ (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧ (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧ (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Claim.Post R z bp s s' := by
  obtain ⟨impl, R, b, z, bp, ret, s, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr⟩ := Wit.nonvacuous
  exact ⟨impl, R, b, z, bp, ret, s, h0, h1, h2, h3, h4, h5, h6, h7, h8, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R z bp s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.IntoBig
