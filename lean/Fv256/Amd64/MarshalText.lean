import Extracted
import Fv256.Spec.MarshalText
import Fv256.Spec.E
import Fv256.Spec.C
import Fv256.Proofs.Common.TextBridge
import Fv256.Spec.Amd64.DecExt
import Fv256.Spec.HexSpec
import Fv256.Spec.Amd64.MarshalText
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.MarshalText

/-!
# amd64: the compiled `(*uint256.Int).MarshalText` implements `Spec.marshalText`  (`Fv256/Spec/MarshalText.lean`)

`z.MarshalText()` (`RAX` = `z`) returns normally (never faults or panics) with a byte slice (pointer, length, capacity) whose
bytes are exactly `Fv256.Spec.marshalText` of the number `*z` (its decimal digits) and a `nil` error. Only the runtime heap and the
callee's stack frame are written. The runtime hypotheses assume `slicebytetostring` and `stringtoslicebyte` obey their allocation contracts.
The proof is `Fv256/Proofs/Amd64/MarshalText.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

open Fv256.E

open Fv256.Amd64.Dec

namespace Fv256.Amd64.MarshalText

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; `z` is a readable 32-byte `uint256.Int` outside the runtime heap and the stack frame; and the runtime model `H` holds of the allocator state (with the allocation sizes this call will request, which depend on the number of decimal digits of `*z`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s (0x378 + 40) ∧ StackWritable s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside ((s.regs 4).toNat - 4608) (4608 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
          (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
          ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
          (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
            H [0, (s.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
              (s.regs 14).toNat ((s.regs 4).toNat - 40 - 0x178 - 8) (rtView rt s.mem)) ∧
          (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
            H [0, (s.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
              (s.regs 14).toNat ((s.regs 4).toNat - 40 - 384 - 0x58) (rtView rt s.mem)) ∧
          (∀ (M : Janus.Arm64.Memory) (p l : Nat),
            MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) →
            StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
            DecAt rt 5163273 5176582 5134938 p l →
            H [0, p, l] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt M))

/-- POSTCONDITION: the returned slice holds exactly the bytes `Spec.marshalText (*z)` (`*z` read BEFORE the call), the error result is `nil`; only the runtime heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) : Prop :=
  BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (Fv256.Spec.marshalText (valueAt s z 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decBytes`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) :
    (BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (decBytes (valueAt s z 32)) ∧
            s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
            MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)])) ↔ Post rt H z s s' := by
  unfold Post Fv256.Spec.marshalText; rw [Fv256.TextBridge.dec_eq]

/-- THE CLAIM: for every runtime whose allocation helpers obey their contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt H z) :=
  (correctness_proof impl rt H z hc hc2).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H z s s').1 hq)

namespace Witness

/-- The preconditions, the `slicebytetostring` and `stringtoslicebyte` contracts (toy runtime blocks, readiness `Hw`), and the readiness hypothesis
for the second call are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (Pre rt H z s) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 ssAddr ∧ RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 stAddr ∧ RtPre64 rt 4096 H stringtoslicebyteSpec s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H z s s' := by
  obtain ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, c6, c7, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, c6, c7, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H z s s').1 hq⟩⟩

end Witness

end Fv256.Amd64.MarshalText
