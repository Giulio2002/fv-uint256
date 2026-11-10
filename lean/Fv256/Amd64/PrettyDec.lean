import Extracted
import Fv256.Spec.PrettyDec
import Fv256.Spec.PrettyMath
import Fv256.Spec.E
import Fv256.Spec.C
import Fv256.Proofs.Common.TextBridge
import Fv256.Spec.Amd64.DecExt
import Fv256.Spec.HexSpec
import Fv256.Spec.Amd64.PrettyDec
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.PrettyDec

/-!
# amd64: the compiled `(*uint256.Int).PrettyDec` implements `Spec.prettyDec`  (`Fv256/Spec/PrettyDec.lean`)

`z.PrettyDec(sep)` returns normally (never faults or panics) with a string whose bytes are exactly `Fv256.Spec.prettyDec` of the
separator `sep` and the number `*z`: its decimal digits grouped in threes from the right, separated by `sep`. Only the runtime heap and the
callee's stack frame are written. The runtime hypothesis assumes `slicebytetostring` obeys its allocation contract.
The proof is `Fv256/Proofs/Amd64/PrettyDec.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

open Fv256.E

open Janus.Contracts.SatAmd64

open Janus.Contracts.Sat (rtW HEAP)

namespace Fv256.Amd64.PrettyDec

/-- PRECONDITION (machine facts only): the stack check passes and the frame is usable; the static data is loaded; `z` is a readable 32-byte `uint256.Int` outside the runtime heap and the stack frame; and the runtime model `H` holds of the allocator state (with the allocation sizes this call will request, which depend on the length of the grouped decimal rendering of `*z`). -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0x378 ∧ StackWritable s 4576 0x18 ∧ Extracted.program.DataLoaded s.mem ∧
          Outside ((s.regs 4).toNat - 4576) (4576 + 0x18) rt ∧
          (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ z.toNat) ∧
          ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16) ∧
          (valueAt s z 32 ≠ 0 →
            H [0, (s.regs 4).toNat - 0xa8 - plen (valueAt s z 32), plen (valueAt s z 32)]
              (s.regs 14).toNat ((s.regs 4).toNat - 0x188) (rtView rt s.mem))

/-- POSTCONDITION: the result string holds exactly the bytes `Spec.prettyDec sep (*z)` (`*z` read BEFORE the call, `sep` the low byte of the argument); only the runtime heap and the callee frame were written. -/
def Post (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64) (s s' : State) : Prop :=
  StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (Fv256.Spec.prettyDec (sep.toNat % 256) (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`prettyBytes`) is equivalent to `Post`. -/
theorem post_iff (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64) (s s' : State) :
    (StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (prettyBytes (sep.toNat % 256) (valueAt s z 32)) ∧
            MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])) ↔ Post rt H z sep s s' := by
  unfold Post; rw [Fv256.TextBridge.prettyDec_eq]

/-- THE CLAIM: for every runtime whose `slicebytetostring` obeys its contract and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, sep]
      (Pre rt H z sep) (Post rt H z sep) :=
  (correctness_proof impl rt H z sep hc).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff rt H z sep s s').1 hq)

namespace Witness

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address, copying the five bytes of `"1,000"`) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z sep : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧
      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, sep] s ∧
    (Pre rt H z sep s) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt H z sep s s' := by
  obtain ⟨impl, rt, H, ret, s, z, sep, c1, c2, c3, c4, c5, hret⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, ret, s, z, sep, c1, c2, c3, c4, c5, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff rt H z sep s s').1 hq⟩⟩

end Witness

end Fv256.Amd64.PrettyDec
