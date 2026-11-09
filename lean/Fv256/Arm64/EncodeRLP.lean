import Extracted
import Fv256.Spec.EncodeRLP
import Fv256.Proofs.Common.ValueBridge
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.EncodeRLP
import Fv256.Proofs.Arm64.EncodeRLPBridge

/-!
# arm64: the compiled `(*uint256.Int).EncodeRLP(w io.Writer) error` implements `Spec.encodeRLP`  (`Fv256/Spec/EncodeRLP.lean`)

`z.EncodeRLP(w)` (`z` in `X0`, the `io.Writer` interface `(tab, w)` in `X1`, `X2`) returns normally (no fault, no panic) obeying the ABI,
calling the writer's `Write` method exactly once and returning its error. WHAT IT WRITES is the specification and is stated in the hypothesis
`hw` (the contract of that one interface call): the bytes passed to `Write` are `Fv256.Spec.encodeRLP x`, the RLP encoding of the number
`x` at `z` (zero for a nil receiver) -- one byte `0x80` for 0, the byte itself below 128, else a length prefix and the minimal big-endian bytes.
The receiver is only read (`z` unchanged); the call allocates two small buffers (explicit `runtime.newobject` contract). SCOPE: the writer
is an arbitrary implementation satisfying `hw`, whose result `R w ptr len cap n e1 e2` is what is returned.
The proof is `Fv256/Proofs/Arm64/EncodeRLP.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/EncodeRLPBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.EncodeRLP

/-- PRECONDITION (machine facts, the allocator-state facts `H`, and the interface-call facts): `stack` is the writer callee's frame size (`≥ 4104`) and its code address `fn` is a valid code pointer; the stack-growth check falls through, the 64 + `stack` byte frame (and 32 bytes above) is writable and aligned, read-only data loaded; the frame is outside `rt`; `z` is nil or addresses 32 readable bytes outside `rt` and disjoint from the frame; the itab word `tab + 24` holds `fn` (readable, outside `rt`, disjoint from the frame); the allocator state `H` holds for the two `newobject` requests (`[33]byte` and `[1]byte` buffers). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (z tab : BitVec 64) (s : State) : Prop :=
  4104 ≤ stack ∧ CodePtrOK fn ∧ GuardOK s 0 ∧ StackOK s (64 + stack) 32 ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 64 - stack) (stack + 96) rt ∧
  (z = 0 ∨ (Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 64 - stack) (stack + 96))) ∧
  Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 64 - stack) (stack + 96) ∧
  tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ Outside (tab.toNat + 24) 8 rt ∧
  s.mem.readLE (tab.toNat + 24) 8 = fn ∧
  H [tyBig] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem) ∧
  H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)

/-- POSTCONDITION: the returned error `(X0, X1)` is the one the writer's call produced (`R w ptr len cap n e1 e2` with `e1`, `e2` the error words); the number at `z` is unchanged; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (stack : Nat) (R : Res) (z w : BitVec 64) (s s' : State) : Prop :=
  (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2) ∧
  (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (fn stack : Nat)
    (R : Res)
    (z tab w : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (Fv256.Spec.encodeRLP (if z.toNat = 0 then 0 else sc.mem.readLE z.toNat 32)) ∧ (sc.regs 3).toNat = (sc.regs 2).toNat)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, w]
      (Pre rt H fn stack z tab) (Post rt stack R z w) :=
  Ensures.mono (correctness_proof impl rt H fn stack R z tab w hnew (by simpa only [Fv256.Proofs.Rlp.rlpBytes_rlpVal] using hw)) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt stack R z w s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res) (z tab w : BitVec 64) (ret : Nat) (s : State), NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (Fv256.Spec.encodeRLP (if z.toNat = 0 then 0 else sc.mem.readLE z.toNat 32)) ∧ (sc.regs 3).toNat = (sc.regs 2).toNat) ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, w] s ∧ Pre rt H fn stack z tab s ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre 4 stack 96 rt (fun sc => sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (Fv256.Spec.encodeRLP (if z.toNat = 0 then 0 else sc.mem.readLE z.toNat 32)) ∧ (sc.regs 3).toNat = (sc.regs 2).toNat) s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt stack R z w s s' := by
  obtain ⟨impl, rt, H, fn, stack, R, z, tab, w, ret, s, h0, h1, h2, h3, h4, h5, h6, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, fn, stack, R, z, tab, w, ret, s, h0, (by simpa only [Fv256.Proofs.Rlp.rlpBytes_rlpVal] using h1), h2, h3, h4, h5, (by simpa only [Fv256.Proofs.Rlp.rlpBytes_rlpVal] using h6), hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt stack R z w s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.EncodeRLP
