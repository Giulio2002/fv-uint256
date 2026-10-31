import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).ExtendSign(x, byteNum *Int) *Int` (arm64): sign extension from byte `byteNum`

**Guarantee.** For all pointers `z` (receiver, `X0`), `x` (`X1`) and `y = byteNum` (`X2`) and every Go call state with the 32 bytes at `z`
writable and those at `x`, `y` readable (below `2^48`), where every pair of the three pointers is equal or disjoint, the call returns
(no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.extendSign` of the numbers at `x`
(the value) and `y` (the byte index, a full 256-bit number: indices of 31 or more leave `x` unchanged) before the call, and no byte
outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` with value `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ExtendSign

set_option maxHeartbeats 64000000 in
theorem correctness (z x y : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
        Aliasing z x ∧ Aliasing z y ∧ Aliasing x y)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.extendSign (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, ⟨hy, hy'⟩, hzx, hzy, hxy⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  · rcases hzy with rfl | hzy
    · simp only [Disjoint] at *
      janus_run [Util.rot3_idx', Util.readLE8_mod]
      · have := (Util.readLE8_lt s.mem z.toNat)
        simp only [Spec.extendSign]
        rw [if_neg (by omega)]
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 0 ∨ b0 = 1 ∨ b0 = 2 ∨ b0 = 3 ∨ b0 = 4 ∨ b0 = 5 ∨ b0 = 6 ∨ b0 = 7 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 0 := h
          have hsh : ((((BitVec.ofNat 64 0).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide
          (try simp only [hsh0])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 0 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 1 := h
          have hsh : ((((BitVec.ofNat 64 1).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 1 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 2 := h
          have hsh : ((((BitVec.ofNat 64 2).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 2 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 3 := h
          have hsh : ((((BitVec.ofNat 64 3).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 3 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 4 := h
          have hsh : ((((BitVec.ofNat 64 4).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 4 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 5 := h
          have hsh : ((((BitVec.ofNat 64 5).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 5 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 6 := h
          have hsh : ((((BitVec.ofNat 64 6).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 6 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 7 := h
          have hsh : ((((BitVec.ofNat 64 7).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 7 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 8 ∨ b0 = 9 ∨ b0 = 10 ∨ b0 = 11 ∨ b0 = 12 ∨ b0 = 13 ∨ b0 = 14 ∨ b0 = 15 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 8 := h
          have hsh : ((((BitVec.ofNat 64 8).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 8 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 9 := h
          have hsh : ((((BitVec.ofNat 64 9).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 9 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 10 := h
          have hsh : ((((BitVec.ofNat 64 10).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 10 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 11 := h
          have hsh : ((((BitVec.ofNat 64 11).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 11 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 12 := h
          have hsh : ((((BitVec.ofNat 64 12).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 12 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 13 := h
          have hsh : ((((BitVec.ofNat 64 13).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 13 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 14 := h
          have hsh : ((((BitVec.ofNat 64 14).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 14 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 15 := h
          have hsh : ((((BitVec.ofNat 64 15).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 15 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 16 ∨ b0 = 17 ∨ b0 = 18 ∨ b0 = 19 ∨ b0 = 20 ∨ b0 = 21 ∨ b0 = 22 ∨ b0 = 23 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 16 := h
          have hsh : ((((BitVec.ofNat 64 16).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 16 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 17 := h
          have hsh : ((((BitVec.ofNat 64 17).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 17 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 18 := h
          have hsh : ((((BitVec.ofNat 64 18).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 18 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 19 := h
          have hsh : ((((BitVec.ofNat 64 19).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 19 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 20 := h
          have hsh : ((((BitVec.ofNat 64 20).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 20 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 21 := h
          have hsh : ((((BitVec.ofNat 64 21).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 21 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 22 := h
          have hsh : ((((BitVec.ofNat 64 22).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 22 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 23 := h
          have hsh : ((((BitVec.ofNat 64 23).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 23 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 24 ∨ b0 = 25 ∨ b0 = 26 ∨ b0 = 27 ∨ b0 = 28 ∨ b0 = 29 ∨ b0 = 30 by omega) with h | h | h | h | h | h | h
        · obtain rfl : b0 = 24 := h
          have hsh : ((((BitVec.ofNat 64 24).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 24 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 25 := h
          have hsh : ((((BitVec.ofNat 64 25).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 25 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 26 := h
          have hsh : ((((BitVec.ofNat 64 26).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 26 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 27 := h
          have hsh : ((((BitVec.ofNat 64 27).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 27 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 28 := h
          have hsh : ((((BitVec.ofNat 64 28).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 28 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 29 := h
          have hsh : ((((BitVec.ofNat 64 29).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 29 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 30 := h
          have hsh : ((((BitVec.ofNat 64 30).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 30 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        simp only [Spec.extendSign]
        rw [if_neg]
        rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega
    · simp only [Disjoint] at *
      janus_run [Util.rot3_idx', Util.readLE8_mod]
      · have := (Util.readLE8_lt s.mem z.toNat)
        simp only [Spec.extendSign]
        rw [if_neg (by omega)]
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem y.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE y.toNat 8 = b0 at *
        rcases (show b0 = 0 ∨ b0 = 1 ∨ b0 = 2 ∨ b0 = 3 ∨ b0 = 4 ∨ b0 = 5 ∨ b0 = 6 ∨ b0 = 7 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 0 := h
          have hsh : ((((BitVec.ofNat 64 0).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide
          (try simp only [hsh0])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 0 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 1 := h
          have hsh : ((((BitVec.ofNat 64 1).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 1 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 2 := h
          have hsh : ((((BitVec.ofNat 64 2).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 2 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 3 := h
          have hsh : ((((BitVec.ofNat 64 3).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 3 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 4 := h
          have hsh : ((((BitVec.ofNat 64 4).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 4 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 5 := h
          have hsh : ((((BitVec.ofNat 64 5).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 5 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 6 := h
          have hsh : ((((BitVec.ofNat 64 6).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 6 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 7 := h
          have hsh : ((((BitVec.ofNat 64 7).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 7 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem y.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE y.toNat 8 = b0 at *
        rcases (show b0 = 8 ∨ b0 = 9 ∨ b0 = 10 ∨ b0 = 11 ∨ b0 = 12 ∨ b0 = 13 ∨ b0 = 14 ∨ b0 = 15 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 8 := h
          have hsh : ((((BitVec.ofNat 64 8).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 8 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 9 := h
          have hsh : ((((BitVec.ofNat 64 9).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 9 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 10 := h
          have hsh : ((((BitVec.ofNat 64 10).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 10 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 11 := h
          have hsh : ((((BitVec.ofNat 64 11).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 11 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 12 := h
          have hsh : ((((BitVec.ofNat 64 12).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 12 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 13 := h
          have hsh : ((((BitVec.ofNat 64 13).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 13 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 14 := h
          have hsh : ((((BitVec.ofNat 64 14).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 14 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 15 := h
          have hsh : ((((BitVec.ofNat 64 15).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 15 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem y.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE y.toNat 8 = b0 at *
        rcases (show b0 = 16 ∨ b0 = 17 ∨ b0 = 18 ∨ b0 = 19 ∨ b0 = 20 ∨ b0 = 21 ∨ b0 = 22 ∨ b0 = 23 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 16 := h
          have hsh : ((((BitVec.ofNat 64 16).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 16 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 17 := h
          have hsh : ((((BitVec.ofNat 64 17).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 17 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 18 := h
          have hsh : ((((BitVec.ofNat 64 18).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 18 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 19 := h
          have hsh : ((((BitVec.ofNat 64 19).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 19 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 20 := h
          have hsh : ((((BitVec.ofNat 64 20).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 20 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 21 := h
          have hsh : ((((BitVec.ofNat 64 21).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 21 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 22 := h
          have hsh : ((((BitVec.ofNat 64 22).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 22 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 23 := h
          have hsh : ((((BitVec.ofNat 64 23).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 23 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem y.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE y.toNat 8 = b0 at *
        rcases (show b0 = 24 ∨ b0 = 25 ∨ b0 = 26 ∨ b0 = 27 ∨ b0 = 28 ∨ b0 = 29 ∨ b0 = 30 by omega) with h | h | h | h | h | h | h
        · obtain rfl : b0 = 24 := h
          have hsh : ((((BitVec.ofNat 64 24).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 24 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 25 := h
          have hsh : ((((BitVec.ofNat 64 25).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 25 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 26 := h
          have hsh : ((((BitVec.ofNat 64 26).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 26 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 27 := h
          have hsh : ((((BitVec.ofNat 64 27).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 27 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 28 := h
          have hsh : ((((BitVec.ofNat 64 28).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 28 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 29 := h
          have hsh : ((((BitVec.ofNat 64 29).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 29 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 30 := h
          have hsh : ((((BitVec.ofNat 64 30).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 30 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        have := (Util.readLE8_lt s.mem y.toNat)
        have := (Util.readLE8_lt s.mem (y.toNat + 8))
        have := (Util.readLE8_lt s.mem (y.toNat + 16))
        have := (Util.readLE8_lt s.mem (y.toNat + 24))
        simp only [Spec.extendSign]
        rw [if_neg]
        rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega
  · rcases hzy with rfl | hzy
    · simp only [Disjoint] at *
      janus_run [Util.rot3_idx', Util.readLE8_mod]
      · have := (Util.readLE8_lt s.mem x.toNat)
        simp only [Spec.extendSign]
        rw [if_neg (by omega)]
      · have := (Util.readLE8_lt s.mem x.toNat)
        have := (Util.readLE8_lt s.mem (x.toNat + 8))
        have := (Util.readLE8_lt s.mem (x.toNat + 16))
        have := (Util.readLE8_lt s.mem (x.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 0 ∨ b0 = 1 ∨ b0 = 2 ∨ b0 = 3 ∨ b0 = 4 ∨ b0 = 5 ∨ b0 = 6 ∨ b0 = 7 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 0 := h
          have hsh : ((((BitVec.ofNat 64 0).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide
          (try simp only [hsh0])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 0 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 1 := h
          have hsh : ((((BitVec.ofNat 64 1).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 1 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 2 := h
          have hsh : ((((BitVec.ofNat 64 2).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 2 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 3 := h
          have hsh : ((((BitVec.ofNat 64 3).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 3 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 4 := h
          have hsh : ((((BitVec.ofNat 64 4).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 4 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 5 := h
          have hsh : ((((BitVec.ofNat 64 5).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 5 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 6 := h
          have hsh : ((((BitVec.ofNat 64 6).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 6 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 7 := h
          have hsh : ((((BitVec.ofNat 64 7).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 7 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem x.toNat)
        have := (Util.readLE8_lt s.mem (x.toNat + 8))
        have := (Util.readLE8_lt s.mem (x.toNat + 16))
        have := (Util.readLE8_lt s.mem (x.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 8 ∨ b0 = 9 ∨ b0 = 10 ∨ b0 = 11 ∨ b0 = 12 ∨ b0 = 13 ∨ b0 = 14 ∨ b0 = 15 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 8 := h
          have hsh : ((((BitVec.ofNat 64 8).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 8 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 9 := h
          have hsh : ((((BitVec.ofNat 64 9).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 9 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 10 := h
          have hsh : ((((BitVec.ofNat 64 10).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 10 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 11 := h
          have hsh : ((((BitVec.ofNat 64 11).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 11 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 12 := h
          have hsh : ((((BitVec.ofNat 64 12).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 12 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 13 := h
          have hsh : ((((BitVec.ofNat 64 13).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 13 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 14 := h
          have hsh : ((((BitVec.ofNat 64 14).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 14 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 15 := h
          have hsh : ((((BitVec.ofNat 64 15).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 15 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem x.toNat)
        have := (Util.readLE8_lt s.mem (x.toNat + 8))
        have := (Util.readLE8_lt s.mem (x.toNat + 16))
        have := (Util.readLE8_lt s.mem (x.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 16 ∨ b0 = 17 ∨ b0 = 18 ∨ b0 = 19 ∨ b0 = 20 ∨ b0 = 21 ∨ b0 = 22 ∨ b0 = 23 by omega) with h | h | h | h | h | h | h | h
        · obtain rfl : b0 = 16 := h
          have hsh : ((((BitVec.ofNat 64 16).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          rw [Util.es_F _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 16 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 17 := h
          have hsh : ((((BitVec.ofNat 64 17).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          rw [Util.es_F _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 17 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 18 := h
          have hsh : ((((BitVec.ofNat 64 18).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          rw [Util.es_F _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 18 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 19 := h
          have hsh : ((((BitVec.ofNat 64 19).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          rw [Util.es_F _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 19 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 20 := h
          have hsh : ((((BitVec.ofNat 64 20).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          rw [Util.es_F _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 20 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 21 := h
          have hsh : ((((BitVec.ofNat 64 21).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          rw [Util.es_F _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 21 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 22 := h
          have hsh : ((((BitVec.ofNat 64 22).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          rw [Util.es_F _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 22 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 23 := h
          have hsh : ((((BitVec.ofNat 64 23).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 56 (by omega) (by omega)]
          rw [Util.es_F _ 56 (by omega) (by omega)]
          simp only [Spec.extendSign, show 23 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem x.toNat)
        have := (Util.readLE8_lt s.mem (x.toNat + 8))
        have := (Util.readLE8_lt s.mem (x.toNat + 16))
        have := (Util.readLE8_lt s.mem (x.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
        simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
        generalize hb : s.mem.readLE z.toNat 8 = b0 at *
        rcases (show b0 = 24 ∨ b0 = 25 ∨ b0 = 26 ∨ b0 = 27 ∨ b0 = 28 ∨ b0 = 29 ∨ b0 = 30 by omega) with h | h | h | h | h | h | h
        · obtain rfl : b0 = 24 := h
          have hsh : ((((BitVec.ofNat 64 24).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 0 (by omega) (by omega)]
          simp only [Spec.extendSign, show 24 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 25 := h
          have hsh : ((((BitVec.ofNat 64 25).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 8 (by omega) (by omega)]
          simp only [Spec.extendSign, show 25 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 26 := h
          have hsh : ((((BitVec.ofNat 64 26).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 16 (by omega) (by omega)]
          simp only [Spec.extendSign, show 26 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 27 := h
          have hsh : ((((BitVec.ofNat 64 27).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 24 (by omega) (by omega)]
          simp only [Spec.extendSign, show 27 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 28 := h
          have hsh : ((((BitVec.ofNat 64 28).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 32 (by omega) (by omega)]
          simp only [Spec.extendSign, show 28 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 29 := h
          have hsh : ((((BitVec.ofNat 64 29).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 40 (by omega) (by omega)]
          simp only [Spec.extendSign, show 29 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
        · obtain rfl : b0 = 30 := h
          have hsh : ((((BitVec.ofNat 64 30).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
          (try simp only [hsh])
          rw [Util.es_E _ 48 (by omega) (by omega)]
          simp only [Spec.extendSign, show 30 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
          (try split) <;> (try split) <;> (try split) <;> omega
      · have := (Util.readLE8_lt s.mem x.toNat)
        have := (Util.readLE8_lt s.mem (x.toNat + 8))
        have := (Util.readLE8_lt s.mem (x.toNat + 16))
        have := (Util.readLE8_lt s.mem (x.toNat + 24))
        have := (Util.readLE8_lt s.mem z.toNat)
        have := (Util.readLE8_lt s.mem (z.toNat + 8))
        have := (Util.readLE8_lt s.mem (z.toNat + 16))
        have := (Util.readLE8_lt s.mem (z.toNat + 24))
        simp only [Spec.extendSign]
        rw [if_neg]
        rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega
    · rcases hxy with rfl | hxy
      · simp only [Disjoint] at *
        janus_run [Util.rot3_idx', Util.readLE8_mod]
        · have := (Util.readLE8_lt s.mem x.toNat)
          simp only [Spec.extendSign]
          rw [if_neg (by omega)]
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem x.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE x.toNat 8 = b0 at *
          rcases (show b0 = 0 ∨ b0 = 1 ∨ b0 = 2 ∨ b0 = 3 ∨ b0 = 4 ∨ b0 = 5 ∨ b0 = 6 ∨ b0 = 7 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 0 := h
            have hsh : ((((BitVec.ofNat 64 0).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide
            (try simp only [hsh0])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 0 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 1 := h
            have hsh : ((((BitVec.ofNat 64 1).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 1 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 2 := h
            have hsh : ((((BitVec.ofNat 64 2).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 2 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 3 := h
            have hsh : ((((BitVec.ofNat 64 3).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 3 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 4 := h
            have hsh : ((((BitVec.ofNat 64 4).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 4 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 5 := h
            have hsh : ((((BitVec.ofNat 64 5).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 5 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 6 := h
            have hsh : ((((BitVec.ofNat 64 6).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 6 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 7 := h
            have hsh : ((((BitVec.ofNat 64 7).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 7 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem x.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE x.toNat 8 = b0 at *
          rcases (show b0 = 8 ∨ b0 = 9 ∨ b0 = 10 ∨ b0 = 11 ∨ b0 = 12 ∨ b0 = 13 ∨ b0 = 14 ∨ b0 = 15 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 8 := h
            have hsh : ((((BitVec.ofNat 64 8).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 8 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 9 := h
            have hsh : ((((BitVec.ofNat 64 9).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 9 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 10 := h
            have hsh : ((((BitVec.ofNat 64 10).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 10 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 11 := h
            have hsh : ((((BitVec.ofNat 64 11).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 11 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 12 := h
            have hsh : ((((BitVec.ofNat 64 12).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 12 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 13 := h
            have hsh : ((((BitVec.ofNat 64 13).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 13 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 14 := h
            have hsh : ((((BitVec.ofNat 64 14).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 14 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 15 := h
            have hsh : ((((BitVec.ofNat 64 15).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 15 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem x.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE x.toNat 8 = b0 at *
          rcases (show b0 = 16 ∨ b0 = 17 ∨ b0 = 18 ∨ b0 = 19 ∨ b0 = 20 ∨ b0 = 21 ∨ b0 = 22 ∨ b0 = 23 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 16 := h
            have hsh : ((((BitVec.ofNat 64 16).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 16 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 17 := h
            have hsh : ((((BitVec.ofNat 64 17).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 17 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 18 := h
            have hsh : ((((BitVec.ofNat 64 18).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 18 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 19 := h
            have hsh : ((((BitVec.ofNat 64 19).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 19 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 20 := h
            have hsh : ((((BitVec.ofNat 64 20).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 20 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 21 := h
            have hsh : ((((BitVec.ofNat 64 21).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 21 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 22 := h
            have hsh : ((((BitVec.ofNat 64 22).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 22 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 23 := h
            have hsh : ((((BitVec.ofNat 64 23).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 23 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem x.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE x.toNat 8 = b0 at *
          rcases (show b0 = 24 ∨ b0 = 25 ∨ b0 = 26 ∨ b0 = 27 ∨ b0 = 28 ∨ b0 = 29 ∨ b0 = 30 by omega) with h | h | h | h | h | h | h
          · obtain rfl : b0 = 24 := h
            have hsh : ((((BitVec.ofNat 64 24).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 24 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 25 := h
            have hsh : ((((BitVec.ofNat 64 25).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 25 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 26 := h
            have hsh : ((((BitVec.ofNat 64 26).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 26 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 27 := h
            have hsh : ((((BitVec.ofNat 64 27).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 27 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 28 := h
            have hsh : ((((BitVec.ofNat 64 28).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 28 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 29 := h
            have hsh : ((((BitVec.ofNat 64 29).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 29 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 30 := h
            have hsh : ((((BitVec.ofNat 64 30).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 30 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          simp only [Spec.extendSign]
          rw [if_neg]
          rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega
      · simp only [Disjoint] at *
        janus_run [Util.rot3_idx', Util.readLE8_mod]
        · have := (Util.readLE8_lt s.mem x.toNat)
          simp only [Spec.extendSign]
          rw [if_neg (by omega)]
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem y.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE y.toNat 8 = b0 at *
          rcases (show b0 = 0 ∨ b0 = 1 ∨ b0 = 2 ∨ b0 = 3 ∨ b0 = 4 ∨ b0 = 5 ∨ b0 = 6 ∨ b0 = 7 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 0 := h
            have hsh : ((((BitVec.ofNat 64 0).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            have hsh0 : (((0#64).rotateRight 61).toNat &&& 56) % 64 = 0 := by decide
            (try simp only [hsh0])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 0 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 1 := h
            have hsh : ((((BitVec.ofNat 64 1).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 1 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 2 := h
            have hsh : ((((BitVec.ofNat 64 2).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 2 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 3 := h
            have hsh : ((((BitVec.ofNat 64 3).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 3 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 4 := h
            have hsh : ((((BitVec.ofNat 64 4).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 4 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 5 := h
            have hsh : ((((BitVec.ofNat 64 5).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 5 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 6 := h
            have hsh : ((((BitVec.ofNat 64 6).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 6 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 7 := h
            have hsh : ((((BitVec.ofNat 64 7).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 7 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem y.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE y.toNat 8 = b0 at *
          rcases (show b0 = 8 ∨ b0 = 9 ∨ b0 = 10 ∨ b0 = 11 ∨ b0 = 12 ∨ b0 = 13 ∨ b0 = 14 ∨ b0 = 15 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 8 := h
            have hsh : ((((BitVec.ofNat 64 8).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 8 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 9 := h
            have hsh : ((((BitVec.ofNat 64 9).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 9 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 10 := h
            have hsh : ((((BitVec.ofNat 64 10).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 10 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 11 := h
            have hsh : ((((BitVec.ofNat 64 11).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 11 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 12 := h
            have hsh : ((((BitVec.ofNat 64 12).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 12 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 13 := h
            have hsh : ((((BitVec.ofNat 64 13).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 13 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 14 := h
            have hsh : ((((BitVec.ofNat 64 14).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 14 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 15 := h
            have hsh : ((((BitVec.ofNat 64 15).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 15 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem y.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE y.toNat 8 = b0 at *
          rcases (show b0 = 16 ∨ b0 = 17 ∨ b0 = 18 ∨ b0 = 19 ∨ b0 = 20 ∨ b0 = 21 ∨ b0 = 22 ∨ b0 = 23 by omega) with h | h | h | h | h | h | h | h
          · obtain rfl : b0 = 16 := h
            have hsh : ((((BitVec.ofNat 64 16).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            rw [Util.es_F _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 16 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 17 := h
            have hsh : ((((BitVec.ofNat 64 17).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            rw [Util.es_F _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 17 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 18 := h
            have hsh : ((((BitVec.ofNat 64 18).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            rw [Util.es_F _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 18 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 19 := h
            have hsh : ((((BitVec.ofNat 64 19).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            rw [Util.es_F _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 19 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 20 := h
            have hsh : ((((BitVec.ofNat 64 20).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            rw [Util.es_F _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 20 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 21 := h
            have hsh : ((((BitVec.ofNat 64 21).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            rw [Util.es_F _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 21 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 22 := h
            have hsh : ((((BitVec.ofNat 64 22).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            rw [Util.es_F _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 22 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 23 := h
            have hsh : ((((BitVec.ofNat 64 23).rotateRight 61).toNat &&& 56) % 64) = 56 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 56 (by omega) (by omega)]
            rw [Util.es_F _ 56 (by omega) (by omega)]
            simp only [Spec.extendSign, show 23 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem y.toNat)
          obtain ⟨hy3, hy1, hy2⟩ := Util.or3_zero _ _ _ ‹_ ||| (_ ||| _) = 0›
          simp only [hy1, hy2, hy3, Nat.mul_zero, Nat.add_zero]
          generalize hb : s.mem.readLE y.toNat 8 = b0 at *
          rcases (show b0 = 24 ∨ b0 = 25 ∨ b0 = 26 ∨ b0 = 27 ∨ b0 = 28 ∨ b0 = 29 ∨ b0 = 30 by omega) with h | h | h | h | h | h | h
          · obtain rfl : b0 = 24 := h
            have hsh : ((((BitVec.ofNat 64 24).rotateRight 61).toNat &&& 56) % 64) = 0 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 0 (by omega) (by omega)]
            simp only [Spec.extendSign, show 24 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 25 := h
            have hsh : ((((BitVec.ofNat 64 25).rotateRight 61).toNat &&& 56) % 64) = 8 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 8 (by omega) (by omega)]
            simp only [Spec.extendSign, show 25 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 26 := h
            have hsh : ((((BitVec.ofNat 64 26).rotateRight 61).toNat &&& 56) % 64) = 16 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 16 (by omega) (by omega)]
            simp only [Spec.extendSign, show 26 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 27 := h
            have hsh : ((((BitVec.ofNat 64 27).rotateRight 61).toNat &&& 56) % 64) = 24 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 24 (by omega) (by omega)]
            simp only [Spec.extendSign, show 27 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 28 := h
            have hsh : ((((BitVec.ofNat 64 28).rotateRight 61).toNat &&& 56) % 64) = 32 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 32 (by omega) (by omega)]
            simp only [Spec.extendSign, show 28 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 29 := h
            have hsh : ((((BitVec.ofNat 64 29).rotateRight 61).toNat &&& 56) % 64) = 40 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 40 (by omega) (by omega)]
            simp only [Spec.extendSign, show 29 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
          · obtain rfl : b0 = 30 := h
            have hsh : ((((BitVec.ofNat 64 30).rotateRight 61).toNat &&& 56) % 64) = 48 := by decide
            (try simp only [hsh])
            rw [Util.es_E _ 48 (by omega) (by omega)]
            simp only [Spec.extendSign, show 30 < 31 from by decide, ite_true, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Spec.W]
            (try split) <;> (try split) <;> (try split) <;> omega
        · have := (Util.readLE8_lt s.mem x.toNat)
          have := (Util.readLE8_lt s.mem (x.toNat + 8))
          have := (Util.readLE8_lt s.mem (x.toNat + 16))
          have := (Util.readLE8_lt s.mem (x.toNat + 24))
          have := (Util.readLE8_lt s.mem y.toNat)
          have := (Util.readLE8_lt s.mem (y.toNat + 8))
          have := (Util.readLE8_lt s.mem (y.toNat + 16))
          have := (Util.readLE8_lt s.mem (y.toNat + 24))
          simp only [Spec.extendSign]
          rw [if_neg]
          rcases Util.or3_ne _ _ _ ‹¬ _ ||| (_ ||| _) = 0› with h | h | h <;> omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x else if i = 2 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Ptr32 s0.mem x false ∧
    Aliasing z x ∧ Aliasing z x ∧ Aliasing x x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inr (by unfold Disjoint32 Disjoint z x; decide), Or.inl rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧
      Aliasing z x ∧ Aliasing z y ∧ Aliasing x y) :=
  ⟨ret, s0, z, x, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.ExtendSign
