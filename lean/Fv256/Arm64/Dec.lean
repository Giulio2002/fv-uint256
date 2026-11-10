import Extracted
import Fv256.Spec.Dec
import Fv256.Spec.E
import Fv256.Spec.C
import Fv256.Proofs.Common.TextBridge
import Fv256.Spec.Arm64.DecExt
import Fv256.Proofs.Legacy.HexSpec
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.Dec

/-!
# arm64: the compiled `(*uint256.Int).Dec` implements `Spec.dec`  (`Fv256/Spec/Dec.lean`)

`z.Dec()` (`X0` = `z`) returns normally (never faults or panics) with a string (pointer and length in the result registers) whose bytes
are exactly `Fv256.Spec.dec` of the number `*z`: its decimal digits, no leading zeros. Only the runtime heap and the callee's stack
frame are written. The runtime hypothesis `hc` assumes `runtime.slicebytetostring` obeys its allocation contract.
The proof is `Fv256/Proofs/Arm64/Dec.lean`.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts

open Fv256.E

open Fv256.Arm64.CallSites

open Janus.Contracts.Sat

namespace Fv256.Arm64.Dec

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; `z` is a readable 32-byte `uint256.Int` outside the runtime heap and the stack frame; and the runtime model `H` holds of the allocator state (with the allocation sizes this call will request, which depend on the number of decimal digits of `*z`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
          Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
          ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
          (2 ^ 64 ≤ val256 s.mem z.toNat →
            H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
              (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
          (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
            H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
              (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem))

/-- POSTCONDITION: the result string holds exactly the bytes `Spec.dec (*z)`, where `*z` is read BEFORE the call; only the runtime heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) : Prop :=
  StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (Fv256.Spec.dec (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decBytes`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (s s' : State) :
    (StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
            MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])) ↔ Post rt H z s s' := by
  unfold Post; rw [Fv256.TextBridge.dec_eq]

/-- THE CLAIM: for every runtime whose `slicebytetostring` obeys its contract and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre rt H z) (Post rt H z) :=
  (correctness_proof impl rt H z hc).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H z s s').1 hq)

namespace Witness

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (Pre rt H z s) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H z s s' := by
  obtain ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, c1, c2, c3, c4, c5, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H z s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.Dec
