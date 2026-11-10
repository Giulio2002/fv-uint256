import Extracted
import Fv256.Spec.MustFromHex
import Fv256.Spec.C
import Fv256.Spec.Arm64.SetFromHexLoops
import Fv256.Spec.Arm64.MustFromHex
import Fv256.Proofs.Common.HexBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.MustFromHex

/-!
# arm64: the compiled `uint256.MustFromHex` implements `Spec.mustFromHex`  (`Fv256/Spec/MustFromHex.lean`)

`MustFromHex(s)` (`X0`, `X1` = `s.ptr`, `s.len`) never faults. For the bytes of `s` it does what `Fv256.Spec.mustFromHex` says: if the
string is a valid hex number it RETURNS a pointer to a fresh 32-byte, 16-aligned `Int` in the runtime's heap holding the number;
otherwise it PANICS with the error value (the package's sentinel error variable). Memory outside the runtime heap and the callee's
stack frame is untouched. `P` is the panic runtime (how a panic is classified); `hnew` assumes `runtime.newobject` obeys its allocation contract.
The proof is `Fv256/Proofs/Arm64/MustFromHex.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic Fv256.C Fv256.Arm64.SetFromHexLoops

open Fv256.Arm64.CallSites

open Janus.Contracts.IfaceModel

namespace Fv256.Arm64.MustFromHex

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; the string `s` is readable and lies outside the runtime heap and the stack frame; the package error variables, their type words and the hex table are readable and outside the heap and frame; the runtime model `H` holds of the allocator state. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
          H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
          Ptr s.mem hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
          Disjoint hp.toNat len.toNat (s.sp.toNat - 4144) 4168 ∧
          s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
          Outside errBase 96 rt ∧ Disjoint errBase 96 (s.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
          Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168 ∧
          (∀ e, e < 6 → s.mem.accessible (s.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
            Outside (s.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
            Disjoint (s.mem.readLE (errAddrOf e) 8 + 8) 8 (s.sp.toNat - 4144) 4168)

/-- POSTCONDITION when the call RETURNS: `Spec.mustFromHex` yields `ok v` (the string is valid), and the result pointer addresses a fresh, aligned, writable 32-byte block inside the heap holding `v`; only the heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.mustFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) with
   | .ok v =>
      ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v
   | .error _ => False) ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])

/-- POSTCONDITION when the call PANICS: `Spec.mustFromHex` yields `error e` (the string is invalid), and the panic value is the error interface value stored in the package variable selected by `e` (via `HexError.tag`). -/
def Panics (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s : State) (v : Janus.Eface) (_ : State) : Prop :=
  match Fv256.Spec.mustFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) with
  | .ok _ => False
  | .error e => v = ⟨s.mem.readLE (s.mem.readLE (errAddrOf e.tag) 8 + 8) 8, s.mem.readLE (errAddrOf e.tag + 8) 8⟩

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s s' : State) :
    ((∃ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v) ∧
            (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
              ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
                s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v) ∧
            MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) ↔ Post rt H hp len s s' := by
  unfold Post Fv256.Spec.mustFromHex Fv256.Spec.fromHex
  rw [Fv256.HexBridge.parseHex_eq, Fv256.HexBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) = r
  rw [← and_assoc]
  apply and_congr_left
  intro _
  cases r with
  | ok v => simp [Fv256.HexBridge.toExcept]
  | error e => simp [Fv256.HexBridge.toExcept]

/-- BRIDGE (not part of the claim): the implementation-shaped panic condition is equivalent to `Panics`. -/
theorem pan_iff (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s : State) (v : Janus.Eface) (s2 : State) :
    (∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e ∧
            v = ⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩) ↔ Panics rt H hp len s v s2 := by
  unfold Panics Fv256.Spec.mustFromHex Fv256.Spec.fromHex
  rw [Fv256.HexBridge.parseHex_eq, Fv256.HexBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) = r
  cases r with
  | ok v => simp [Fv256.HexBridge.toExcept]
  | error e => simp [Fv256.HexBridge.toExcept]

/-- THE CLAIM: for every panic runtime `P`, every runtime whose `newobject` obeys its contract and every call meeting `Pre`, the compiled code either returns in a state meeting `Post` or panics with a value meeting `Panics`, never faulting (ABI obeyed on return). -/
theorem correctness (P : PanicRuntime) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [hp, len]
      (Pre rt H hp len) (fun _ => goClass P) (Post rt H hp len) (Panics rt H hp len) :=
  (correctness_proof P impl rt H hp len hnew).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H hp len s s').1 hq)
    (fun s v s2 _ hq => (pan_iff rt H hp len s v s2).1 hq)

namespace Witness

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (P : PanicRuntime) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [hp, len] s ∧
    (pinPanicRuntime P ∧
    Pre rt H hp len s) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ Post rt H hp len s s'
      | .panicked v s' => Panics rt H hp len s v s'
      | .goexited _ => False := by
  obtain ⟨impl, rt, H, hp, len, P, ret, s, c1, c2, c3, c4, c5, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, hp, len, P, ret, s, c1, c2, c3, c4, c5, hret.mono fun o ho => by
    cases o with
    | returned s' => exact ⟨ho.1, (post_iff rt H hp len s s').1 ho.2⟩
    | panicked v s' => exact (pan_iff rt H hp len s v s').1 ho
    | goexited s' => exact ho⟩

end Witness

end Fv256.Arm64.MustFromHex
