import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Spec.Amd64.Byte

/-!
# `(*uint256.Int).Byte(n *Int) *Int` (amd64): `z = the n-th byte (from the most significant end) of z`

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) and every Go call state such that the return-address slot
is writable, the 32 bytes at `z` are writable, those at `x` readable (below `2^48`), `z` does not overlap the return-address
slot, and `z`, `x` are equal or disjoint, the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number
at `z` afterwards is `Fv256.Spec.byte` of the number at `x` (the index) and the number at `z` before the call, and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `0`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Byte

set_option maxHeartbeats 8000000 in
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.byte (valueAt s x 32) (valueAt s z 32) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint, Alias] at *
  rcases hzx with rfl | hzx
  · try simp only [Disjoint, Alias] at *
    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *); generalize hN : s.mem.readLE z.toNat 8 = N at *
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        have e1 : N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8 = N := (by omega)
        have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
        rw [e2]
        rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        have hq : (18446744073709551616 - (18446744073709551613 + N / 8) % 18446744073709551616) % 18446744073709551616 = 3 - N / 8 := (by omega)
        rw [hq]
        have hr7 : N % 8 = 7 := (by omega)
        rw [hr7]
        rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *); generalize hN : s.mem.readLE z.toNat 8 = N at *
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        have e1 : N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8 = N := (by omega)
        have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
        rw [e2]
        rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        have hq : (18446744073709551616 - (18446744073709551613 + N / 8) % 18446744073709551616) % 18446744073709551616 = 3 - N / 8 := (by omega)
        rw [hq]
        have hr : (18446744073709551616 - (18446744073709551560 + N % 8 * 8)) % 64 = 8 * (7 - N % 8) := (by omega)
        rw [hr]
        rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *)
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        simp only [Spec.byte]
        split <;> omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *)
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        simp only [Spec.byte]
        split <;> omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
  · try simp only [Disjoint, Alias] at *
    janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *); generalize hN : s.mem.readLE x.toNat 8 = N at *
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        have e1 : N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 = N := (by omega)
        have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
        rw [e2]
        rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        have hq : (18446744073709551616 - (18446744073709551613 + N / 8) % 18446744073709551616) % 18446744073709551616 = 3 - N / 8 := (by omega)
        rw [hq]
        have hr7 : N % 8 = 7 := (by omega)
        rw [hr7]
        rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *); generalize hN : s.mem.readLE x.toNat 8 = N at *
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        have e1 : N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 = N := (by omega)
        have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
        rw [e2]
        rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        have hq : (18446744073709551616 - (18446744073709551613 + N / 8) % 18446744073709551616) % 18446744073709551616 = 3 - N / 8 := (by omega)
        rw [hq]
        have hr : (18446744073709551616 - (18446744073709551560 + N % 8 * 8)) % 64 = 8 * (7 - N % 8) := (by omega)
        rw [hr]
        rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
        · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero]; simp [hN]; omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *)
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        simp only [Spec.byte]
        split <;> omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]
    · refine ⟨?_, ?_⟩
      · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); (try simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.or_eq_zero_iff] at *)
        (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero])
        simp only [Spec.byte]
        split <;> omega
      · simp (disch := omega) only [Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp else 0,
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
        valueAt s' z 32 = Spec.byte (valueAt s x 32) (valueAt s z 32) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.Byte
