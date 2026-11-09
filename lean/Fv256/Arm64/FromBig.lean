import Extracted
import Fv256.Spec.FromBig
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.FromBig
import Fv256.Proofs.Arm64.FromBigBridge

/-!
# arm64: the compiled `uint256.FromBig(b *big.Int) (*Int, bool)` implements `Spec.fromBig`  (`Fv256/Spec/FromBig.lean`)

`FromBig(x)` (`x` in `X0`) returns normally (no fault, no panic) obeying the ABI. For a nil `x` it returns `(nil, false)`. Otherwise it
allocates a fresh 32-byte `Int` (explicit runtime contract: `runtime.newobject` returns a 16-aligned, accessible block inside the heap
ranges `rt`) holding `(Fv256.Spec.fromBig b len).1` (the integer value `b` of the `big.Int`, modulo `2^256`) and returns it with the overflow
flag `(Fv256.Spec.fromBig b len).2` (more than four limbs) in `X1`. SCOPE: the `big.Int` is well formed (sign byte 0 or 1, limb pointer
and count read from the struct, limbs readable).
The proof is `Fv256/Proofs/Arm64/FromBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/FromBigBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Arm64.CallSites

namespace Fv256.Arm64.FromBig

/-- PRECONDITION (machine facts only, plus the allocator-state fact `H`): the stack-growth check falls through; the 4144-byte frame window below `SP` and the 24 bytes above it are writable and aligned; read-only data loaded; frame outside `rt`; the frame pointer is the caller's (`X29 = SP - 8`); `H` holds for the `runtime.newobject` request. When `x` is non-nil: the `big.Int` struct at `x` is 32 readable bytes with sign byte 0 or 1, limb pointer `pw`, limb count `len`; the `8 * len` limb bytes at `pw` are readable; struct and limbs are outside `rt` and disjoint from the frame. -/
def Pre (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
  Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
  H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
  (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
    s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
    Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
    Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168)

/-- POSTCONDITION: nil `x` gives `(nil, false)` (`X0 = 0`, `X1 = 0`). Otherwise `X0` points (`ptr`) to a fresh accessible 32-byte block inside `rt` holding the number `(Spec.fromBig b len).1` and `X1` is `(Spec.fromBig b len).2` as 0/1, where `b` is the integer value of the `big.Int` read BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  let r := Fv256.Spec.fromBig b len.toNat
  (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 1 = 0) ∧
  (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
    s'.mem.accessible ptr 32 true = true ∧
    val256 s'.mem ptr = r.1 ∧ (s'.regs 1).toNat = (if r.2 then 1 else 0) ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (x pw len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (Pre rt H x pw len) (Post rt x pw len) :=
  Ensures.mono (correctness_proof impl rt H x pw len hnew) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt x pw len s s').1 q)

namespace Witness

open Fv256.Arm64.FromBig.Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State), NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧ (pinBitVec64 pw ∧ pinBitVec64 len ∧ Pre rt H x pw len s) ∧ (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt x pw len s s' := by
  obtain ⟨impl, rt, H, x, pw, len, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, x, pw, len, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt x pw len s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.FromBig
