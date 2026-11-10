import Extracted
import Fv256.Spec.Value
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.Value
import Fv256.Proofs.Amd64.ValueBridge

/-!
# amd64: the compiled `(*uint256.Int).Value() (driver.Value, error)` implements `Spec.value`  (`Fv256/Spec/Value.lean`)

`z.Value()` (`z` in `RAX`) returns normally (no fault, no panic) obeying the ABI with the interface value `(type, data)` = (`RAX`, `RBX`) of
a `string` and a nil error (`RCX = RDI = 0`): `RAX` is the type descriptor of `string` and `RBX` a box (inside the heap ranges) holding
the string header `(p, l)` whose bytes are `Fv256.Spec.value x`, the decimal digits of the number `x` at `z` (read before the call).
SCOPE (explicit runtime contracts, in `Pre`): the live-runtime contracts of `slicebytetostring` (used by `Dec`) and `convTstring`
(boxing the string); the heap-state facts they need (`HL`, `DecAt`) and the digit-count `decLen`, now stated with `Spec.value`.
The proof is `Fv256/Proofs/Amd64/Value.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/ValueBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec
open Fv256.Amd64.SbtsG

namespace Fv256.Amd64.Value

/-- PRECONDITION (machine facts plus the runtime-contract state the two callees need): the stack-growth check falls through and the 4600-byte frame is writable; read-only data loaded; `g` and the frame lie outside the heap ranges `rt`; the three static digit tables are outside `rt`; `RSP` 8-aligned; `z` addresses 32 readable bytes outside the frame; the heap-state predicates `HL` for the `slicebytetostring` calls (when `x ≥ 2^64`, resp. `100 ≤ x < 2^64`, where the digit count is `(Spec.value x).length`); and the second-call hypothesis: whenever the first call leaves memory `M` as the digit-string `Spec.value x` in a fresh buffer, the `convTstring` call state is live. -/
def Pre (R : RtInv) (z : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4600 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ StackWritable s 4600 8 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside ((s.regs 4).toNat - 4600) (4600 + 8) R.rt ∧ Outside 5163273 256 R.rt ∧ Outside 5176582 256 R.rt ∧ Outside 5134938 256 R.rt ∧
  (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
  (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
    HL R [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length), (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length]
      (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem)) ∧
  (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
    HL R [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length), (Fv256.Spec.value (s.mem.readLE z.toNat 32)).length]
      (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem)) ∧
  (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
    (s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem M [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
    StrOut M p l (Fv256.Spec.value (s.mem.readLE z.toNat 32)) →
    DecAt R.rt 5163273 5176582 5134938 p l →
    (100 ≤ s.mem.readLE z.toNat 32 →
      R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
    ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 14).toNat M
        (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
      (InRanges p l R.rt → InRanges p l L))

/-- POSTCONDITION: `RAX` is the type descriptor of `string`; `RBX` points to a box holding a string header `(p, l)` whose `l` bytes at `p` are `Spec.value x` for the number `x` at `z` BEFORE the call; the error is nil (`RCX = RDI = 0`); memory changed only inside the heap ranges and the callee frame. -/
def Post (R : RtInv) (z : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
  (∃ p l, BoxWords' R.rt s'.mem (s'.regs 3).toNat [p, l] ∧ StrOut s'.mem p l (Fv256.Spec.value (valueAt s z 32))) ∧
  s'.regs 1 = 0 ∧ s'.regs 7 = 0 ∧
  MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Amd64.Segment)
    (R : RtInv)
    (z : BitVec 64)
    (hc0 : RtLiveContract64 (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)
    (hc2 : RtLiveContract64 (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre R z) (Post R z) :=
  Ensures.mono (correctness_proof impl R z hc0 hc2) (fun s h => (Bridge.pre_iff R z s).2 h)
    (fun s s' _ q => (Bridge.post_iff R z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (ret : Nat) (s : Amd64.State) (z : BitVec 64), RtLiveContract64 (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧ RtLiveContract64 (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre R z s ∧ 100 ≤ s.mem.readLE z.toNat 32 ∧ (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 ssAddr ∧ RtLivePre64 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 s_c) ∧ (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 cvAddr ∧ RtLivePre64 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R z s s' := by
  obtain ⟨impl, R, ret, s, z, h0, h1, h2, h3, h4, h5, h6, h7, hr⟩ := Wit.nonvacuous
  exact ⟨impl, R, ret, s, z, h0, h1, h2, h3, (Bridge.pre_iff R z s).1 h4, h5, h6, h7, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R z s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.Value
