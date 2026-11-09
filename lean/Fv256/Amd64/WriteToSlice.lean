import Extracted
import Fv256.Spec.WriteToSlice
import Fv256.Proofs.Common.BytesBridge
import Fv256.Proofs.Amd64.WriteToSlice
import Fv256.Proofs.Amd64.WriteToSliceBridge

/-!
# amd64: the compiled `(*uint256.Int).WriteToSlice(dest []byte)` implements `Spec.writeToSlice`  (`Fv256/Spec/WriteToSlice.lean`)

`z.WriteToSlice(dest)` (`z` in `RAX`, the slice `dest` = pointer `d`, length, capacity in `RBX`, `RCX`, `RDI`) returns normally (no fault,
no panic) obeying the ABI; the first `min(len, 32)` bytes of `dest` are `Fv256.Spec.writeToSlice x len` (the low `min(len, 32)` bytes of
the number `x` at `z`, big-endian; a longer `dest` keeps its tail untouched), and nothing else except the callee frame changes.
SCOPE: `len < 2^48` and `len ≤ cap` (well-formed slice header).
The proof is `Fv256/Proofs/Amd64/WriteToSlice.lean`; the equivalence of the readable byte-list form of the postcondition with the number-reading
form the proof uses is `Fv256/Proofs/Amd64/WriteToSliceBridge.lean`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToSlice

/-- PRECONDITION (machine facts only; the two length facts are the slice-header contract): the return-address slot and the frame `[RSP-8, RSP+24)` are writable; `z` addresses 32 readable bytes and `d` `len` writable bytes; `len < 2^48` and `len ≤ cap`; `z`, `d[0, len)` and the frame are pairwise disjoint. -/
def Pre (z d len cap : BitVec 64) (s : State) : Prop :=
  StackWritable s 8 24 ∧ Buffer s z 32 false ∧ len.toNat < 2 ^ 48 ∧ Buffer s d len.toNat true ∧
  (z.toNat + 32 ≤ d.toNat ∨ d.toNat + len.toNat ≤ z.toNat) ∧
  (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
  (d.toNat + len.toNat ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat) ∧
  len.toNat ≤ cap.toNat

/-- POSTCONDITION: the first `min len 32` bytes at `d` are `Spec.writeToSlice` of the number at `z` BEFORE the call; no byte outside them and the callee frame changed. -/
def Post (z d len : BitVec 64) (s s' : State) : Prop :=
  (List.range (min len.toNat 32)).map (fun i => s'.mem.readLE (d.toNat + i) 1) = Fv256.Spec.writeToSlice (valueAt s z 32) len.toNat ∧
  Fv256.Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) ((s.regs regSP).toNat - 8) 32

/-- THE CLAIM: every call meeting `Pre` returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (z d len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (Pre z d len cap) (Post z d len) :=
  Ensures.mono (correctness_proof z d len cap) (fun _ h => h)
    (fun s s' _ q => (Bridge.post_iff z d len s s').1 q)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

/-- NON-VACUITY: a concrete machine state satisfies `Pre` and its call returns with `Post`, so `Pre` is not unsatisfiable and `correctness` is not empty. -/
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z d : BitVec 64), RetAddr Extracted.program ret ∧ CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s ∧ Pre z d (8 : BitVec 64) (8 : BitVec 64) s ∧ Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Post z d (8 : BitVec 64) s s' := by
  obtain ⟨ret, s, z, d, h0, h1, h2, hr⟩ := Wit.nonvacuous
  exact ⟨ret, s, z, d, h0, h1, h2, hr.mono fun s' hq => ⟨hq.1, (Bridge.post_iff z d (8 : BitVec 64) s s').1 hq.2⟩⟩

end Witness

end Fv256.Amd64.WriteToSlice
