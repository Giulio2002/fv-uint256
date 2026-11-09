import Extracted
import Fv256.Spec.FromBig
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.FromBig
import Fv256.Proofs.Amd64.FromBigBridge

/-!
# amd64: the compiled `uint256.FromBig(b *big.Int) (*Int, bool)` implements `Spec.fromBig`  (`Fv256/Spec/FromBig.lean`)

`FromBig(x)` (`x` in `RAX`) returns normally (no fault, no panic) obeying the ABI. For a nil `x` it returns `(nil, false)`. Otherwise it
allocates a fresh 32-byte `Int` (explicit runtime contract: `runtime.newobject` returns a 16-aligned, accessible block inside the heap
ranges `rt`) holding `(Fv256.Spec.fromBig b len).1` (the integer value `b` of the `big.Int`, modulo `2^256`) and returns it with the overflow
flag `(Fv256.Spec.fromBig b len).2` (more than four limbs) in `BL`. SCOPE: the `big.Int` is well formed (sign byte 0 or 1, limb pointer
and count read from the struct, limbs readable).
The proof is `Fv256/Proofs/Amd64/FromBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/FromBigBridge.lean`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.FromBig

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

/-- POSTCONDITION: nil `x` gives `(nil, false)` (`RAX = 0`, `RBX = 0`). Otherwise `RAX` points (`ptr`) to a fresh accessible 32-byte block inside `rt` holding the number `(Spec.fromBig b len).1` and `BL` is `(Spec.fromBig b len).2` as 0/1, where `b` is the integer value of the `big.Int` read BEFORE the call; memory changed only inside `rt` and the callee frame. -/
def Post (rt : List (Nat × Nat)) (x pw len : BitVec 64) (s s' : State) : Prop :=
  let b := Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat
  let r := Fv256.Spec.fromBig b len.toNat
  (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
  (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
    s'.mem.accessible ptr 32 true = true ∧
    s'.mem.readLE ptr 32 = r.1 ∧ (s'.regs 3).toNat % 256 = (if r.2 then 1 else 0) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness 
    (impl : List Janus.Amd64.Segment)
    (rt : List (Nat × Nat))
    (H : RtReady)
    (x pw len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (Pre rt H x pw len) (Post rt x pw len) :=
  Ensures.mono (correctness_proof impl rt H x pw len hnew) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff rt x pw len s s').1 q)

namespace Witness

open Fv256.Amd64.FromBig.Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State), NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧ (∃ s_c : Janus.Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧ RetAddr (Extracted.program.link impl) ret ∧ CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧ (pinBitVec64 pw ∧ pinBitVec64 len ∧ Pre rt H x pw len s) ∧ Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post rt x pw len s s' := by
  obtain ⟨impl, rt, H, x, pw, len, ret, s, h0, h1, h2, h3, h4, hr⟩ := Wit.nonvacuous
  exact ⟨impl, rt, H, x, pw, len, ret, s, h0, h1, h2, h3, h4, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff rt x pw len s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.FromBig
