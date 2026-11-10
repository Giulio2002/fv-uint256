import Extracted
import Fv256.Spec.FromHex
import Fv256.Spec.C
import Fv256.Spec.Arm64.SetFromHexLoops
import Fv256.Spec.Arm64.FromHex
import Fv256.Proofs.Common.HexBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.FromHex

/-!
# arm64: the compiled `uint256.FromHex` implements `Spec.fromHex`  (`Fv256/Spec/FromHex.lean`)

`FromHex(s)` (`X0`, `X1` = `s.ptr`, `s.len`) returns normally (never faults or panics). Its outcome is exactly `Fv256.Spec.fromHex` of the
bytes of `s`: for a valid hex string it returns `(z, nil)` where `z` is a fresh 32-byte, 16-aligned `Int` in the runtime's heap holding the
number; otherwise `(nil, err)` with `err` the package error variable for the reported error. Memory outside the runtime heap and
the callee's stack frame is untouched. The runtime hypothesis `hnew` assumes `runtime.newobject` behaves as its allocation contract.
The proof is `Fv256/Proofs/Arm64/FromHex.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Arm64.SetFromHexLoops

open Fv256.Arm64.CallSites

open Janus.Contracts.IfaceModel

namespace Fv256.Arm64.FromHex

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; the string `s` is readable and lies outside the runtime heap and the stack frame; the package error variables and the hex table are readable, non-nil and outside the heap and frame; the runtime model `H` holds of the allocator state. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s : State) : Prop :=
  GuardOK s 48 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
          H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
          Ptr s.mem hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
          Disjoint hp.toNat len.toNat (s.sp.toNat - 4144) 4168 ∧
          s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
          Outside errBase 96 rt ∧ Disjoint errBase 96 (s.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
          Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168

/-- POSTCONDITION: for `Spec.fromHex = ok v`: the result pointer (first result register) addresses a fresh, aligned, writable 32-byte block inside the heap holding `v`, with `err = nil`; for `error e`: the pointer is `nil` and `err` is the error variable selected by `e` (via `HexError.tag`); only the heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.fromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) with
   | .ok v =>
      ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0
   | .error e =>
      s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag) 8) ∧
          s'.regs 2 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag + 8) 8)) ∧
  MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`parseHex`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (s s' : State) :
    ((∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
              ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
                s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∧
            (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
              s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 2 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
            MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) ↔ Post rt H hp len s s' := by
  unfold Post Fv256.Spec.fromHex
  rw [Fv256.HexBridge.parseHex_eq, Fv256.HexBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem hp.toNat len.toNat) = r
  rw [← and_assoc]
  apply and_congr_left
  intro _
  cases r with
  | ok v => simp [Fv256.HexBridge.toExcept]
  | error e => simp [Fv256.HexBridge.toExcept]

/-- THE CLAIM: for every runtime whose `newobject` obeys its contract and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [hp, len]
      (Pre rt H hp len) (Post rt H hp len) :=
  (correctness_proof impl rt H hp len hnew).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H hp len s s').1 hq)

namespace Witness

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [hp, len] s ∧
    (Pre rt H hp len s) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H hp len s s' := by
  obtain ⟨impl, rt, H, hp, len, ret, s, c1, c2, c3, c4, c5, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, hp, len, ret, s, c1, c2, c3, c4, c5, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H hp len s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.FromHex
