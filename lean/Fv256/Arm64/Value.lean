import Extracted
import Fv256.Spec.Value
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.Value
import Fv256.Proofs.Arm64.ValueBridge

/-!
# arm64: the compiled `(*uint256.Int).Value() (driver.Value, error)` implements `Spec.value`  (`Fv256/Spec/Value.lean`)

`z.Value()` (`z` in `X0`) returns normally (no fault, no panic) obeying the ABI with the interface value `(type, data)` = (`X0`, `X1`) of
a `string` and a nil error (`X2 = X3 = 0`): `X0` is the type descriptor of `string` and `X1` a box (inside the heap ranges) holding
the string header `(p, l)` whose bytes are `Fv256.Spec.value x`, the decimal digits of the number `x` at `z` (read before the call).
SCOPE (explicit runtime contracts, in `Pre`): the live-runtime contracts of `slicebytetostring` (used by `Dec`) and `convTstring`
(boxing the string); the heap-state facts they need (`HL`, `DecAt`) and the digit-count `decLen`, now stated with `Spec.value`.
The proof is `Fv256/Proofs/Arm64/Value.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/ValueBridge.lean`.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Value

/-- PRECONDITION (machine facts plus the runtime-contract state the two callees need): the stack-growth check falls through and the 4640-byte frame is writable and aligned; read-only data loaded; `g` and the frame lie outside the heap ranges `rt`; the three static digit tables are outside `rt`; `z` addresses 32 readable bytes disjoint from the frame; the heap-state predicates `HL` for the `slicebytetostring` calls (when `x ≥ 2^64`, resp. `100 ≤ x < 2^64`, where the digit count is `(Spec.value x).length`); and the second-call hypothesis: whenever the first call leaves memory `M` as the digit-string `Spec.value x` in a fresh buffer, the `convTstring` call state is live. -/
def Pre (R : RtInv) (z : BitVec 64) (s : State) : Prop :=
  GuardOK s 4608 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
  Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
  ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
  (2 ^ 64 ≤ val256 s.mem z.toNat →
    HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - (Fv256.Spec.value (val256 s.mem z.toNat)).length), (Fv256.Spec.value (val256 s.mem z.toNat)).length]
      (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
  (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
    HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - (Fv256.Spec.value (val256 s.mem z.toNat)).length), (Fv256.Spec.value (val256 s.mem z.toNat)).length]
      (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
  (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
    MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
    (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
    StrOut M p l (Fv256.Spec.value (val256 s.mem z.toNat)) →
    DecAt R.rt 989280 1002589 960826 p l →
    (100 ≤ val256 s.mem z.toNat →
      R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
    ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
        [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
      (InRanges p l R.rt → InRanges p l L))

/-- POSTCONDITION: `X0` is the type descriptor of `string`; `X1` points to a box holding a string header `(p, l)` whose `l` bytes at `p` are `Spec.value x` for the number `x` at `z` BEFORE the call; the error is nil (`X2 = X3 = 0`); memory changed only inside the heap ranges and the callee frame. -/
def Post (R : RtInv) (z : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
  (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (Fv256.Spec.value (val256 s.mem z.toNat))) ∧
  s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
  MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (R : RtInv)
    (z : BitVec 64)
    (hc0 : RtLiveContract (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)
    (hc2 : RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (Pre R z) (Post R z) :=
  Ensures.mono (correctness_proof impl R z hc0 hc2) (fun s h => (Bridge.pre_iff R z s).2 h)
    (fun s s' _ q => (Bridge.post_iff R z s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (ret : Nat) (s : State) (z : BitVec 64), RtLiveContract (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧ RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧ Pre R z s ∧ 100 ≤ val256 s.mem z.toNat ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtLivePre 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 s_c) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 cvAddr ∧ RtLivePre 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R z s s' := by
  obtain ⟨impl, R, ret, s, z, h0, h1, h2, h3, h4, h5, h6, h7, hr⟩ := Wit.nonvacuous
  exact ⟨impl, R, ret, s, z, h0, h1, h2, h3, (Bridge.pre_iff R z s).1 h4, h5, h6, h7, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff R z s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.Value
