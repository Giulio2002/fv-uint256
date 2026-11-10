import Extracted
import Fv256.Spec.MarshalText
import Fv256.Spec.E
import Fv256.Spec.C
import Fv256.Proofs.Common.TextBridge
import Fv256.Spec.Arm64.DecExt
import Fv256.Spec.HexSpec
import Fv256.Spec.Arm64.MarshalText
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.MarshalText

/-!
# arm64: the compiled `(*uint256.Int).MarshalText` implements `Spec.marshalText`  (`Fv256/Spec/MarshalText.lean`)

`z.MarshalText()` (`X0` = `z`) returns normally (never faults or panics) with a byte slice (pointer, length, capacity) whose
bytes are exactly `Fv256.Spec.marshalText` of the number `*z` (its decimal digits) and a `nil` error. Only the runtime heap and the
callee's stack frame are written. The runtime hypotheses assume `slicebytetostring` and `stringtoslicebyte` obey their allocation contracts.
The proof is `Fv256/Proofs/Arm64/MarshalText.lean`.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

open Fv256.E

open Fv256.Arm64.Dec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalText

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; `z` is a readable 32-byte `uint256.Int` outside the runtime heap and the stack frame; and the runtime model `H` holds of the allocator state (with the allocation sizes this call will request, which depend on the number of decimal digits of `*z`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s (688 + 48) ∧ StackOK s 4656 8 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside (s.sp.toNat - 4656) (4656 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
          Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
          ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
          (2 ^ 64 ≤ val256 s.mem z.toNat →
            H [0, s.sp.toNat - 48 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
              (s.regs 28).toNat (s.sp.toNat - 48 - 384) (rtView rt s.mem)) ∧
          (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
            H [0, s.sp.toNat - 48 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
              (s.regs 28).toNat (s.sp.toNat - 48 - 384 - 96) (rtView rt s.mem)) ∧
          (∀ (M : Janus.Arm64.Memory) (p l : Nat),
            MemFrame s.mem M (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)]) →
            StrOut M p l (decBytes (val256 s.mem z.toNat)) →
            DecAt rt 989280 1002589 960826 p l →
            H [0, p, l] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt M))

/-- POSTCONDITION: the returned slice holds exactly the bytes `Spec.marshalText (*z)` (`*z` read BEFORE the call), the error result is `nil`; only the runtime heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) : Prop :=
  BytesHold s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat (Fv256.Spec.marshalText (val256 s.mem z.toNat)) ∧
        s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decBytes`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) :
    (BytesHold s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat (decBytes (val256 s.mem z.toNat)) ∧
            s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
            MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)])) ↔ Post rt H z s s' := by
  unfold Post Fv256.Spec.marshalText; rw [Fv256.TextBridge.dec_eq]

/-- THE CLAIM: for every runtime whose allocation helpers obey their contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt H z) :=
  (correctness_proof impl rt H z hc hc2).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H z s s').1 hq)

namespace Witness

/-- The preconditions, the `slicebytetostring` and `stringtoslicebyte` contracts (toy runtime blocks, readiness `Hw`) and the readiness
hypothesis for the second call are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (Pre rt H z s) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 stAddr ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H z s s' := by
  obtain ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, c6, c7, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, c6, c7, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H z s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.MarshalText
