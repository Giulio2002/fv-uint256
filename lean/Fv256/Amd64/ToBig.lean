import Extracted
import Fv256.Spec.ToBig
import Fv256.Spec.BigIntAt
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.ToBig
import Fv256.Proofs.Amd64.ToBigBridge

/-!
# amd64: the compiled `(*uint256.Int).ToBig() *big.Int` implements `Spec.toBig`  (`Fv256/Spec/ToBig.lean`)

`z.ToBig()` (`z` in `RAX`) returns normally (no fault, no panic) obeying the ABI. For a nil `z` it returns nil (`RAX = 0`). Otherwise it
returns (`RAX = P`) a fresh well-formed `big.Int` (a 32-byte struct plus a 32-byte limb array, both allocated by `runtime.newobject`; the write
barrier is run when enabled) whose integer value is `Fv256.Spec.toBig x`, the number `x` at `z` read before the call. SCOPE (explicit
runtime contracts `hnew`, `hwb1`, `hwb2`): the live-runtime models of `runtime.newobject` and `runtime.gcWriteBarrier1/2` over the runtime
state `R` with invariant budget `b`; the code segments `impl` supplying them lie apart from the program (`hI`).
The proof is `Fv256/Proofs/Amd64/ToBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/ToBigBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel
open Fv256.Amd64.IntoBig (flagAddr bigType arrType BigObj)

namespace Fv256.Amd64.ToBig

/-- PRECONDITION (machine facts plus the live-runtime state the allocator and write-barrier contracts need): the stack-growth check falls through; the 4168-byte frame (and 8 bytes above) is writable and `RSP` 8-aligned; read-only data loaded; the frame and the goroutine slot at `R14+16` are outside the runtime ranges and apart from each other; the write-barrier flag is readable; the two type descriptors (`big.Int`, `[4]Word`) are outside the runtime ranges; the runtime accepts the two `newobject` and two write-barrier calls (`R.ok`); the runtime invariant `R.inv` holds with budget `b` for two blocks (`32` scan, `32` noscan); when `z` is non-nil it addresses 32 readable bytes outside the runtime ranges and the frame. -/
def Pre (R : RtInv) (b : Nat) (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4168 ∧ StackWritable s 4168 8 ∧ (s.regs 4).toNat % 8 = 0 ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside ((s.regs 4).toNat - 4168) 4176 R.rt ∧
  Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4168) 4168 ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
  s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
  blockSize 32 false + blockSize 32 true ≤ b ∧
  (z.toNat ≠ 0 → Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧
    Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4168) 4168)

/-- POSTCONDITION: nil `z` gives nil (`RAX = 0`); otherwise `RAX = P` where the object at `P` is a well-formed `big.Int` of integer value `Spec.toBig` of the number at `z` BEFORE the call; memory changed only inside the runtime ranges and the callee frame. -/
def Post (R : RtInv) (z : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.regs 0 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ Fv256.Spec.BigIntAt s'.mem P (Fv256.Spec.toBig (val256 s.mem z.toNat))) ∧
  MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Amd64.Segment)
    (R : RtInv)
    (b : Nat)
    (z : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre R b z) (Post R z) :=
  Ensures.mono (correctness_proof impl R b z hI hnew hwb1 hwb2) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff R z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64
open Fv256.CallSites

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z : BitVec 64) (ret : Nat) (s : State), Amd64.ImplApart Extracted.program impl ∧ NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧ WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧ WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧ (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧ (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧ (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre R b z s ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R z s s' := by
  obtain ⟨impl, R, b, z, ret, s, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hr⟩ := Wit.nonvacuous
  exact ⟨impl, R, b, z, ret, s, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R z s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.ToBig
