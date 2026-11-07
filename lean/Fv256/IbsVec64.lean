import Janus
open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
namespace Fv256.IndexByte64

/-- The byte predicate of a 32-byte block held in two registers. -/
def blk (x1 x2 c : Nat) (i : Nat) : Bool :=
  if i < 16 then decide (elem x1 8 i = c % 256) else decide (elem x2 8 (i - 16) = c % 256)

/-- The bytes of the magic constant `0x40100401` replicated by `DUP v5.4s`: `1, 4, 16, 64, 1, ...`. -/
theorem mask_elems : ∀ i < 16, elem (ofElems 32 4 fun _ => 1074791425) 8 i = 4 ^ (i % 4) := by
  decide

/-- **The syndrome.** What `AND` with the magic constant and two `ADDP .16B` compute from the
two `CMEQ` masks of a 32-byte block held in `x1:x2`, read back as `UMOV x6, v6.d[0]`: two bits
per byte, bit `2i` set iff byte `i` equals `c`. The left side is exactly the term the executor
produces. -/
theorem syndrome (x1 x2 c : Nat) :
    elem
      (threeSameOp false 0 23 128
        (threeSameOp false 0 23 128
            ((threeSameOp true 0 17 128 x1
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            ((threeSameOp true 0 17 128 x2
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            0 %
          340282366920938463463374607431768211456)
        (threeSameOp false 0 23 128
            ((threeSameOp true 0 17 128 x1
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            ((threeSameOp true 0 17 128 x2
                    ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0 %
                  340282366920938463463374607431768211456 &&&
                (ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) %
              340282366920938463463374607431768211456)
            0 %
          340282366920938463463374607431768211456)
        0)
      64 0 =
    synd (blk x1 x2 c) 32 := by
  rw [elem_64_bytes]
  simp (disch := decide) only [elem_mod_2_128, elem_addp, pairElem, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub, Nat.reducePow, Nat.reduceLT, ite_true, ite_false, elem_and, elem_cmeq,
    elem_ofElems]
  simp (disch := decide) only [mask_elems, Nat.reduceMod, Nat.reducePow, ite_land_nat, Nat.reduceAnd]
  simp (disch := decide) only [ite_add_ite_mod]
  simp (disch := decide) only [ite4_mod]
  simp only [ite_eq_mul_toNat, synd, blk, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false, Nat.reduceSub]
  omega

/-- A vector of all-zero masks is zero. -/
theorem maskSum_eq_zero (f : Nat → Bool) (n : Nat) (h : ∀ k < n, f k = false) : maskSum f n = 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [maskSum, h 0 (by omega), Bool.toNat_false, Nat.mul_zero, Nat.zero_add]
    rw [ih _ (fun k hk => h (k + 1) (by omega))]

/-- "No byte of the block matches", grouped the way the quick test sees the bytes. -/
theorem blk_split (x1 x2 c : Nat) :
    (∀ i < 32, blk x1 x2 c i = false) ↔
      (∀ k < 8, decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256) = false ∧
        decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256) = false) := by
  constructor
  · intro h k hk
    have h1 := h k (by omega); have h2 := h (8 + k) (by omega)
    have h3 := h (16 + k) (by omega); have h4 := h (24 + k) (by omega)
    simp only [blk, show k < 16 by omega, show 8 + k < 16 by omega, show ¬ 16 + k < 16 by omega,
      show ¬ 24 + k < 16 by omega, ite_true, ite_false, decide_eq_false_iff_not,
      show 16 + k - 16 = k by omega, show 24 + k - 16 = 8 + k by omega] at h1 h2 h3 h4
    simp only [decide_eq_false_iff_not, not_or]
    exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · intro h i hi
    simp only [decide_eq_false_iff_not, not_or] at h
    simp only [blk]
    split
    · rcases (by omega : i < 8 ∨ 8 ≤ i) with h' | h'
      · simpa using (h i h').1.1
      · have := (h (i - 8) (by omega)).2.1; rw [show 8 + (i - 8) = i by omega] at this; simpa using this
    · rcases (by omega : i < 24 ∨ 24 ≤ i) with h' | h'
      · simpa using (h (i - 16) (by omega)).1.2
      · have := (h (i - 24) (by omega)).2.2
        rw [show 8 + (i - 24) = i - 16 by omega] at this; simpa using this

/-- `maskSum f 8` written out the way `loopTest`'s hypothesis has it (each mask scaled by its
byte position), so the quick test's sum is matched by rewriting instead of by `omega` over the
unfolded sums (which took about 45 s of this file's check). -/
theorem maskSum_eight (f : Nat → Bool) :
    maskSum f 8 = 255 * (f 0).toNat + 256 * (255 * (f 1).toNat) + 65536 * (255 * (f 2).toNat) +
      16777216 * (255 * (f 3).toNat) + 4294967296 * (255 * (f 4).toNat) +
      1099511627776 * (255 * (f 5).toNat) + 281474976710656 * (255 * (f 6).toNat) +
      72057594037927936 * (255 * (f 7).toNat) := by
  simp only [maskSum, Nat.reduceAdd]; omega

/-- **The quick test.** `ORR` of the two `CMEQ` masks, `ADDP .2D` and `UMOV` give a value that is
zero iff no byte of the 32-byte block `x1:x2` equals `c` (adding the two 64-bit halves cannot
cancel, because both are vectors of `0x00`/`0xFF` bytes: `maskSum_add_mod`). The left side is
exactly the branch condition of the executor's `CBZ`. -/
theorem loopTest (x1 x2 c : Nat) :
    ((elem (threeSameOp true 0 17 128 x1 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 0 |||
          elem (threeSameOp true 0 17 128 x2 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 0) +
        (elem (threeSameOp true 0 17 128 x1 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 1 |||
          elem (threeSameOp true 0 17 128 x2 ((ofElems 8 16 fun _ => c) % 340282366920938463463374607431768211456) 0) 64 1)) %
      18446744073709551616 = 0 ↔ ∀ i < 32, blk x1 x2 c i = false := by
  rw [← elem_or, ← elem_or, elem_64_bytes, elem_64_bytes]
  simp (disch := decide) only [elem_or, elem_cmeq, elem_mod_2_128, elem_ofElems, Nat.reduceMul, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, ite_lor_ite]
  simp only [ite_eq_mul_toNat]
  rw [blk_split]
  constructor
  · intro h
    have := maskSum_add_mod (fun k => decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256))
      (fun k => decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256)) 8 (by
        simp only [maskSum_eight, Nat.reduceAdd, Nat.reducePow]; exact h)
    exact this
  · intro h
    have h1 := maskSum_eq_zero (fun k => decide (elem x1 8 k = c % 256 ∨ elem x2 8 k = c % 256)) 8
      (fun k hk => (h k hk).1)
    have h2 := maskSum_eq_zero (fun k => decide (elem x1 8 (8 + k) = c % 256 ∨ elem x2 8 (8 + k) = c % 256)) 8
      (fun k hk => (h k hk).2)
    simp only [maskSum_eight, Nat.reduceAdd] at h1 h2
    rw [h1, h2]


/-- The block predicate on loaded memory is the byte comparison. -/
theorem blk_readLE (m : Memory) {a b : Nat} (c : Nat) (h : b = a + 16) {i : Nat} (hi : i < 32) :
    blk (m.readLE a 16) (m.readLE b 16) c i = decide (m.readLE (a + i) 1 = c % 256) := by
  subst h
  unfold blk
  split
  · rw [elem_readLE_8 m (by omega)]
  · rw [elem_readLE_8 m (by omega), show a + 16 + (i - 16) = a + i by omega]


end Fv256.IndexByte64
