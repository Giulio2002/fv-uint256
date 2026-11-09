import Extracted
import Fv256.Spec.MustFromBig
import Fv256.Proofs.Common.BigBridge
import Fv256.Proofs.Arm64.MustFromBig
import Fv256.Proofs.Arm64.MustFromBigBridge

/-!
# arm64: the compiled `uint256.MustFromBig` implements `Spec.mustFromBig`  (`Fv256/Spec/MustFromBig.lean`)

`MustFromBig(x)` (`x` in `X0`) either returns normally or PANICS, obeying the ABI. For a nil `x` it returns nil. Otherwise: with at most four
64-bit limbs (`Spec.mustFromBig b len = some v`) it returns a fresh 32-byte `Int` (explicit runtime contract: `runtime.newobject`
returns a 16-aligned, accessible block inside the heap ranges `rt`) holding `Spec.setFromBig b` (the integer value `b` of the `big.Int`
modulo `2^256`); with more than four limbs (`Spec.mustFromBig b len = none`) it panics with the Go string `"overflow"`
(`panicType`/`panicData`). SCOPE: the `big.Int` is well formed (sign byte 0 or 1, limb pointer and count read from the struct, limbs
readable); the panic runtime `P` is an arbitrary one (`goClass P` classifies the outcome). The proof is `Fv256/Proofs/Arm64/MustFromBig.lean`;
the equivalence of the readable postconditions with the proof's forms is `Fv256/Proofs/Arm64/MustFromBigBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MustFromBig

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4144-byte frame window below `SP` and the 24 bytes above it are writable and aligned; read-only data loaded; frame outside `rt`; the frame pointer is the caller's (`X29 = SP - 8`); `H` holds for the `runtime.newobject` request. When `x` is non-nil: the `big.Int` struct at `x` is 32 readable bytes with sign byte 0 or 1, limb pointer `pw`, limb count `len`; the `8 * len` limb bytes at `pw` are readable; struct and limbs are outside `rt` and disjoint from the frame. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168)

/-- POSTCONDITION (the call returns): a nil `x` returns nil (`X0 = 0`); otherwise `MustFromBig` did not panic, i.e. `Spec.mustFromBig b len` is `some _` (at most four limbs), and `X0` points (`ptr`) to a fresh accessible 32-byte block inside `rt` holding `Spec.setFromBig b` (that value), where `b` is the integer value of the `big.Int` read BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  (x.toNat = 0 ∨ (Fv256.Spec.mustFromBig b len.toNat).isSome) ∧
  (x.toNat = 0 → s'.regs 0 = 0) ∧
  (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
    s'.mem.accessible ptr 32 true = true ∧
    val256 s'.mem ptr = Fv256.Spec.setFromBig b ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))

/-- PANIC POSTCONDITION: the call panics exactly when `x` is non-nil and `Spec.mustFromBig b len = none` (more than four limbs), with the
panic value `"overflow"` (`panicType`, `panicData`). -/
def Panics (x pw len : BitVec 64) (s : State) (v : Eface) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  x.toNat ≠ 0 ∧ (Fv256.Spec.mustFromBig b len.toNat).isNone ∧ v = ⟨panicType, panicData⟩

/-- THE CLAIM: every call meeting `Pre` either returns (ABI obeyed) in a state meeting `Post` or panics in the way `Panics` describes. -/
theorem correctness (P : PanicRuntime) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x]
      (Pre rt H x pw len) (fun _ => goClass P) (Post rt x pw len) (fun s v _ => Panics x pw len s v) :=
  EnsuresGo.mono (correctness_proof P impl rt H x pw len hnew) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt x pw len s s').1 q) (fun s v s' _ q => (Bridge.pan_iff x pw len s v).1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (with a toy allocator and a concrete panic runtime) satisfies `Pre` and its call has the outcome
that `Post` (return) or `Panics` allows, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (P : PanicRuntime) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State), NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧ (pinPanicRuntime P ∧ pinBitVec64 pw ∧ pinBitVec64 len ∧ Pre rt H x pw len s) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o => match o with | .returned s' => ABIReturn s s' ∧ Post rt x pw len s s' | .panicked v s' => Panics x pw len s v | .goexited _ => False := by
  obtain ⟨impl, rt, H, x, P, pw, len, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, x, P, pw, len, ret, s, h0, h1, h2, h3, h4,
    hr.mono fun o ho => by
      cases o with
      | returned s' => exact ⟨ho.1, (Bridge.post_iff rt x pw len s s').1 ho.2⟩
      | panicked v s' => exact (Bridge.pan_iff x pw len s v).1 ho
      | goexited _ => exact ho⟩

end Witness

end Fv256.Arm64.MustFromBig
