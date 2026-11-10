import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).ReverseBytes(x *Int) *Int` (amd64)

**Spec (documented).** "ReverseBytes sets z to the value of x with x's 32-byte representation reversed." The 32-byte
representation of an `Int` in memory is its four little-endian limbs, i.e. little-endian bytes `b0..b31`; reversing it gives
`b31..b0`, whose little-endian reading is the big-endian reading `Fv256.Spec.fromBE` of `b0..b31`.

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`), the return-address slot writable, the 32 bytes at `z`
writable and those at `x` readable (below `2^48`), `z` not overlapping the return-address slot, `z` and `x` equal or disjoint:
the call returns, obeys the ABI, returns `z`, the number at `z` afterwards is `Spec.fromBE` of the 32 bytes at `x` (read before
the call), and no byte outside `z[0..32)` changes.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ReverseBytes

/-- equal or disjoint 32-byte objects -/
def Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32

theorem correctness_proof (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.fromBE (fun i => s.mem.readLE (x.toNat + i) 1) 32 ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint, Alias] at *
  rcases hzx with rfl | hzx
  all_goals first | (exfalso; omega) | (janus64_run [Util.readLE_32]; first | (have a0 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat) 8); have a1 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 8) 8); have a2 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 16) 8); have a3 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 24) 8); refine ⟨?_, ?_⟩; (· rw [Util.be32_rev]; simp only [Nat.reducePow] at a0 a1 a2 a3; omega); (· simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self])) | (have a0 := Util.revBytes_lt 8 (s.mem.readLE (x.toNat) 8); have a1 := Util.revBytes_lt 8 (s.mem.readLE (x.toNat + 8) 8); have a2 := Util.revBytes_lt 8 (s.mem.readLE (x.toNat + 16) 8); have a3 := Util.revBytes_lt 8 (s.mem.readLE (x.toNat + 24) 8); refine ⟨?_, ?_⟩; (· rw [Util.be32_rev]; simp only [Nat.reducePow] at a0 a1 a2 a3; omega); (· simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self])))

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x 
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.fromBE (fun i => s.mem.readLE (x.toNat + i) 1) 32 ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness_proof z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness_proof z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  try simp only [valueAt]
  decide

end Wit

end Fv256.Amd64.ReverseBytes
