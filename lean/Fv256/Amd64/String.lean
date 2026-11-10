import Extracted
import Fv256.Spec.String
import Fv256.Spec.E
import Fv256.Spec.C
import Fv256.Proofs.Common.TextBridge
import Fv256.Spec.Amd64.DecExt
import Fv256.Proofs.Legacy.HexSpec
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.String

/-!
# amd64: the compiled `(*uint256.Int).String` implements `Spec.string`  (`Fv256/Spec/String.lean`)

`z.String()` (`RAX` = `z`) returns normally (never faults or panics) with a string whose bytes are exactly `Fv256.Spec.string` of the
number `*z`, i.e. its decimal digits. Only the runtime heap and the callee's stack frame are written. The runtime hypothesis `hc` assumes `runtime.slicebytetostring` obeys its allocation contract.
The proof is `Fv256/Proofs/Amd64/String.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

open Fv256.E

open Fv256.Amd64.Dec

open Janus.Contracts.SatAmd64

open Janus.Contracts.Sat (rtW H0)

namespace Fv256.Amd64.String

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; `z` is a readable 32-byte `uint256.Int` outside the runtime heap and the stack frame; and the runtime model `H` holds of the allocator state (with the allocation sizes this call will request, which depend on the number of decimal digits of `*z`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s (0x378 + 24) ∧ StackWritable s 4592 8 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside ((s.regs 4).toNat - 4592) (4592 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
          (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
          ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
          (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
            H [0, (s.regs 4).toNat - 24 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
              (s.regs 14).toNat ((s.regs 4).toNat - 24 - 0x178 - 8) (rtView rt s.mem)) ∧
          (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
            H [0, (s.regs 4).toNat - 24 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
              (s.regs 14).toNat ((s.regs 4).toNat - 24 - 384 - 0x58) (rtView rt s.mem))

/-- POSTCONDITION: the result string holds exactly the bytes `Spec.string (*z)`, where `*z` is read BEFORE the call; only the runtime heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) : Prop :=
  StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (Fv256.Spec.string (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decBytes`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) :
    (StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
            MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)])) ↔ Post rt H z s s' := by
  unfold Post Fv256.Spec.string; rw [Fv256.TextBridge.dec_eq]

/-- THE CLAIM: for every runtime whose `slicebytetostring` obeys its contract and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt H z) :=
  (correctness_proof impl rt H z hc).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H z s s').1 hq)

namespace Witness

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧
      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (Pre rt H z s) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H z s s' := by
  obtain ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H z s s').1 hq⟩⟩

end Witness

end Fv256.Amd64.String
