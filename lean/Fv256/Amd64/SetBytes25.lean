import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetBytes25(in []byte) *Int` (amd64)

**Guarantee (`correctness`).** For every receiver `z` (`RAX`) and slice `in = (ptr, len, cap)` (`RBX`, `RCX`, `RDI`) with
`len ≥ 25`, such that the return-address slot and the frame window `[RSP-8, RSP+24)` are writable, the 32 bytes at `z` are
writable, the 25 bytes at `ptr` are readable, and neither overlaps the other or the frame window, every call returns (no fault,
no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.fromBE` of the first 25 bytes of
the slice (big-endian, bytes read before the call), and no byte changes outside `z[0..32)` and the frame window
(`Fv256.Util.OnlyWrites2`).

**Guarantee (`panics`).** If `len < 25` the call reaches the bounds-check panic stub (`Panics`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes25

set_option maxHeartbeats 8000000 in
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => 25 ≤ len.toNat ∧ StackWritable s 8 24 ∧ Buffer s z 32 true ∧ Buffer s ptr 25 false ∧
        (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 25 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (ptr.toNat + 25 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 25 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 8) 32) := by
  intro ret hret s hs ⟨hl, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3⟩
  janus64_intro hs
  simp only [regSP] at hacc hlow hnw hd2 hd3
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · have := Util.rd1_lt s.mem (ptr.toNat); have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd1_lt s.mem (ptr.toNat + 2); have := Util.rd1_lt s.mem (ptr.toNat + 3); have := Util.rd1_lt s.mem (ptr.toNat + 4); have := Util.rd1_lt s.mem (ptr.toNat + 5); have := Util.rd1_lt s.mem (ptr.toNat + 6); have := Util.rd1_lt s.mem (ptr.toNat + 7); have := Util.rd1_lt s.mem (ptr.toNat + 8); have := Util.rd1_lt s.mem (ptr.toNat + 9); have := Util.rd1_lt s.mem (ptr.toNat + 10); have := Util.rd1_lt s.mem (ptr.toNat + 11); have := Util.rd1_lt s.mem (ptr.toNat + 12); have := Util.rd1_lt s.mem (ptr.toNat + 13); have := Util.rd1_lt s.mem (ptr.toNat + 14); have := Util.rd1_lt s.mem (ptr.toNat + 15); have := Util.rd1_lt s.mem (ptr.toNat + 16); have := Util.rd1_lt s.mem (ptr.toNat + 17); have := Util.rd1_lt s.mem (ptr.toNat + 18); have := Util.rd1_lt s.mem (ptr.toNat + 19); have := Util.rd1_lt s.mem (ptr.toNat + 20); have := Util.rd1_lt s.mem (ptr.toNat + 21); have := Util.rd1_lt s.mem (ptr.toNat + 22); have := Util.rd1_lt s.mem (ptr.toNat + 23); have := Util.rd1_lt s.mem (ptr.toNat + 24); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

/-- Out of bounds (`len < 25`): `runtime.panicBounds`. -/
theorem panics (z ptr len cap : BitVec 64) (hl : len.toNat < 25) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hpre : StackWritable s 16 24) : Panics (Extracted.program.withExit ret) s := by
  janus64_intro hs
  obtain ⟨hle, hnw, hacc⟩ := hpre
  simp only [regSP] at hacc hle hnw
  janus64_run

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def ptr : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then ptr else if i = 1 then 25 else if i = 7 then 25
      else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 25, 25] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : 25 ≤ (25 : BitVec 64).toNat ∧ StackWritable s0 8 24 ∧ Buffer s0 z 32 true ∧ Buffer s0 ptr 25 false ∧
    (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 25 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (ptr.toNat + 25 ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24 ≤ ptr.toNat) :=
  ⟨by decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (25 ≤ len.toNat ∧ StackWritable s 8 24 ∧ Buffer s z 32 true ∧ Buffer s ptr 25 false ∧
        (z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 25 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (ptr.toNat + 25 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 25 ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 8) 32 :=
  ⟨ret, s0, z, ptr, 25, 25, hret, setup, hpre,
    correctness z ptr 25 25 ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      valueAt s' z 32 = Fv256.Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + i) 1) 25 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 ((s0.regs regSP).toNat - 8) 32 :=
  (correctness z ptr 25 25 ret hret s0 setup hpre)

end Witness

end Fv256.Amd64.SetBytes25
