import Extracted
import Fv256.Spec.SetFromBig
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.SetFromBig
import Fv256.Proofs.Amd64.SetFromBigBridge

/-!
# amd64: the compiled `(*uint256.Int).SetFromBig(b *big.Int) bool` implements `Spec.setFromBig`  (`Fv256/Spec/SetFromBig.lean`)

`z.SetFromBig(b)` (`z`, `b` in `RAX`, `RBX`) returns normally (no fault, no panic) obeying the ABI with the overflow flag in `AL`
(`Spec.setFromBigOverflow len`: more than four limbs), leaves `Fv256.Spec.setFromBig b` (the integer value `b` of the `big.Int`,
modulo `2^256`) in `z`, and writes nothing but `z[0, 32)`. SCOPE (explicit runtime contract of the `big.Int` layout): the sign byte is 0
or 1, the limb pointer and count are read from the struct, and the `len` limbs are readable.
The proof is `Fv256/Proofs/Amd64/SetFromBig.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/SetFromBigBridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetFromBig

/-- PRECONDITION (machine facts only): the return-address slot is writable; `z` addresses 32 writable bytes and the `big.Int` struct `b` 32 readable bytes; the struct's sign byte is 0 or 1, its limb pointer is `pw` and its limb count `len`; the `8 * len` limb bytes at `pw` are readable; `z` is disjoint from the struct, from the limbs and from the return-address slot. -/
def Pre (z b pw len : BitVec 64) (s : State) : Prop :=
  StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
  s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
  Buffer s pw (8 * len.toNat) false ∧
  Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * len.toNat) ∧ Disjoint z 32 (s.regs regSP) 8

/-- POSTCONDITION: `AL` is the overflow flag; the number at `z` is `Spec.setFromBig` of the integer value of the `big.Int` (sign flag, `len` limbs read BEFORE the call); only `z[0, 32)` was written. -/
def Post (z b pw len : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat % 256 = (if Fv256.Spec.setFromBigOverflow len.toNat then 1 else 0) ∧
  valueAt s' z 32 = Fv256.Spec.setFromBig (Fv256.Spec.bigValue (s.mem.readLE b.toNat 1 == 1) (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
  Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z b pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b]
      (Pre z b pw len) (Post z b pw len) :=
  Ensures.mono (correctness_proof z b pw len) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z b pw len s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b pw : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b] s ∧ Pre z b pw (2 : BitVec 64) s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z b pw (2 : BitVec 64) s s' := by
  obtain ⟨ret, s, z, b, pw, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, b, pw, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z b pw (2 : BitVec 64) s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.SetFromBig
