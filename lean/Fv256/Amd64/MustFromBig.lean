import Extracted
import Fv256.Spec.MustFromBig
import Fv256.Proofs.Common.BigBridge
import Fv256.Proofs.Amd64.MustFromBig
import Fv256.Proofs.Amd64.MustFromBigBridge

/-!
# amd64: the compiled `uint256.MustFromBig` implements `Spec.mustFromBig`  (`Fv256/Spec/MustFromBig.lean`)

`MustFromBig(x)` (`x` in `RAX`) either returns normally or PANICS, obeying the ABI. For a nil `x` it returns nil. Otherwise: with at most four
64-bit limbs (`Spec.mustFromBig b len = some v`) it returns a fresh 32-byte `Int` (explicit runtime contract: `runtime.newobject`
returns a 16-aligned, accessible block inside the heap ranges `rt`) holding `Spec.setFromBig b` (the integer value `b` of the `big.Int`
modulo `2^256`); with more than four limbs (`Spec.mustFromBig b len = none`) it panics with the Go string `"overflow"`
(`panicType`/`panicData`). SCOPE: the `big.Int` is well formed (sign byte 0 or 1, limb pointer and count read from the struct, limbs
readable); the panic runtime `P` is an arbitrary one (`goClass P` classifies the outcome). The proof is `Fv256/Proofs/Amd64/MustFromBig.lean`;
the equivalence of the readable postconditions with the proof's forms is `Fv256/Proofs/Amd64/MustFromBigBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64

namespace Fv256.Amd64.MustFromBig

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4136-byte frame window below `RSP` and the 24 bytes above it are writable; read-only data loaded; frame outside `rt`; `RSP` 8-aligned; `H` holds for the `runtime.newobject` request. When `x` is non-nil: the `big.Int` struct at `x` is 32 readable bytes with sign byte 0 or 1, limb pointer `pw`, limb count `len`; the `8 * len` limb bytes at `pw` are readable; struct and limbs are outside `rt` and the frame. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Buffer s x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Buffer s pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          (x.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ x.toNat) ∧
          (pw.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ pw.toNat))

/-- POSTCONDITION (the call returns): a nil `x` returns nil (`RAX = 0`); otherwise `MustFromBig` did not panic, i.e. `Spec.mustFromBig b len` is `some _` (at most four limbs), and `RAX` points (`ptr`) to a fresh accessible 32-byte block inside `rt` holding `Spec.setFromBig b` (that value), where `b` is the integer value of the `big.Int` read BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  (x.toNat = 0 ∨ (Fv256.Spec.mustFromBig b len.toNat).isSome) ∧
  (x.toNat = 0 → s'.regs 0 = 0) ∧
  (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
    s'.mem.accessible ptr 32 true = true ∧
    s'.mem.readLE ptr 32 = Fv256.Spec.setFromBig b ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))

/-- PANIC POSTCONDITION: the call panics exactly when `x` is non-nil and `Spec.mustFromBig b len = none` (more than four limbs), with the
panic value `"overflow"` (`panicType`, `panicData`). -/
def Panics (x pw len : BitVec 64) (s : State) (v : Eface) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  x.toNat ≠ 0 ∧ (Fv256.Spec.mustFromBig b len.toNat).isNone ∧ v = ⟨panicType, panicData⟩

/-- THE CLAIM: every call meeting `Pre` either returns (ABI obeyed) in a state meeting `Post` or panics in the way `Panics` describes. -/
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x]
      (Pre rt H x pw len) (fun _ => goClass P) (Post rt x pw len) (fun s v _ => Panics x pw len s v) :=
  EnsuresGo.mono (correctness_proof P impl rt H x pw len hnew) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt x pw len s s').1 q) (fun s v s' _ q => (Bridge.pan_iff x pw len s v).1 q)

namespace Witness

open Fv256.Amd64.MustFromBig.Wit
open Fv256.CallSites

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state (with a toy allocator and a concrete panic runtime) satisfies `Pre` and its call has the outcome
that `Post` (return) or `Panics` allows, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (P : Janus.Spec.PanicRuntime) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State), NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧ (pinJanusSpecPanicRuntime P ∧ pinBitVec64 pw ∧ pinBitVec64 len ∧ Pre rt H x pw len s) ∧ GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o => match o with | .returned s' => ABIReturn s s' ∧ Post rt x pw len s s' | .panicked v s' => Panics x pw len s v | .goexited _ => False := by
  obtain ⟨impl, rt, H, x, P, pw, len, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, x, P, pw, len, ret, s, h0, h1, h2, h3, h4,
    hr.mono fun o ho => by
      cases o with
      | returned s' => exact ⟨ho.1, (Bridge.post_iff rt x pw len s s').1 ho.2⟩
      | panicked v s' => exact (Bridge.pan_iff x pw len s v).1 ho
      | goexited _ => exact ho⟩

end Witness

end Fv256.Amd64.MustFromBig
