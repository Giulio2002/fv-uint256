import Extracted
import Fv256.Spec.CmpBig
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Arm64.CmpBig
import Fv256.Proofs.Arm64.CmpBigBridge

/-!
# arm64: the compiled `(*uint256.Int).CmpBig(x *big.Int) (r int)` implements `Spec.cmpBig`  (`Fv256/Spec/CmpBig.lean`)

`z.CmpBig(x)` (`z`, `x` in `X0`, `X1`) returns normally (no fault, no panic) obeying the ABI with `X0 = Fv256.Spec.cmpBig z x` as a
signed 64-bit integer (-1, 0 or +1), changing only its own stack frame and result slot. SCOPE (explicit runtime contract): the `big.Int`
is well formed: sign byte 0 or 1, limb pointer and count read from the struct, the limbs readable, and NORMALIZED (no leading zero limb:
`len = 0` or the top limb is non-zero), as every `big.Int` produced by the `math/big` API is.
The proof is `Fv256/Proofs/Arm64/CmpBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Arm64/CmpBigBridge.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.CmpBig

/-- PRECONDITION (machine facts only): stack-growth check falls through; frame `[SP-72, SP+16)` writable and aligned; `z` and the `big.Int` struct `x` address 32 readable bytes each; sign byte 0 or 1, limb pointer `pw`, limb count `len`, the `8 * len` limb bytes readable; normalized magnitude (`len = 0` or top limb non-zero); `z`, the struct and the limbs do not overlap the frame; the frame pointer is the caller's (`X29 = SP - 8`). -/
def Pre (z x pw len : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 72 16 ∧ Ptr32 s.mem z false ∧ Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
  s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
  Ptr s.mem pw (8 * len.toNat) false ∧
  (len.toNat = 0 ∨ s.mem.readLE (pw.toNat + 8 * (len.toNat - 1)) 8 ≠ 0) ∧
  Disjoint z.toNat 32 (s.sp.toNat - 72) 88 ∧ Disjoint x.toNat 32 (s.sp.toNat - 72) 88 ∧
  Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 72) 88 ∧ s.regs 29 = s.sp - 8#64

/-- POSTCONDITION: `X0` is `Spec.cmpBig` of the number at `z` and the integer value of the `big.Int` (all read BEFORE the call), as a 64-bit two's-complement integer; memory changed only in the result slot `[SP+8, SP+16)` and the callee frame `[SP-72, SP)`. -/
def Post (z x pw len : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = BitVec.ofInt 64
    (Fv256.Spec.cmpBig (val256 s.mem z.toNat) (Fv256.Spec.bigValue (s.mem.readLE x.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat)) ∧
  MemFrame s.mem s'.mem [(s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat - 72, s.sp.toNat)]

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z x pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (Pre z x pw len) (Post z x pw len) :=
  Ensures.mono (correctness_proof z x pw len) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z x pw len s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x pw : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧ Pre z x pw (2 : BitVec 64) s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z x pw (2 : BitVec 64) s s' := by
  obtain ⟨ret, s, z, x, pw, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, x, pw, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z x pw (2 : BitVec 64) s s').1 hq.2⟩⟩

end Witness

end Fv256.Arm64.CmpBig
