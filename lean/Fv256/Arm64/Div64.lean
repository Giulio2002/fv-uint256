import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB
import Fv256.Div64Math

/-!
# `math/bits.Div64(hi, lo, y uint64) (quo, rem uint64)` (arm64, Go 1.26)

`div64_summary` is the callee summary of the software 128/64 division the arm64 compiler emits (there is no 128/64
divide instruction): for `y != 0` and `hi < y` (the documented non-panicking domain) it returns
`quo = (hi * 2^64 + lo) / y` and `rem = (hi * 2^64 + lo) % y`, preserving `SP`, `X18`, `X28`, `X29`, `X30` and
every register except `X0..X12`, `X16`, writing memory only in the 16 bytes of its frame.  The panic outcomes
(`y = 0` and `y <= hi`) are the separate `EnsuresGo` theorem `Fv256.Arm64.Div64.panics`.

The proof follows Go's Knuth/Hacker's-Delight `divlu`: normalise `y` by `clz`, two 32-bit quotient digits, each
corrected by a bounded loop (`loop1`, `loop2`, proved by induction on the trial digit); the mathematics is in
`Fv256.Div64Math`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Div64

theorem rr_mono {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop} (h : ReachesRet p ret s Q)
    (hQ : ∀ S, Q S → Q' S) : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hp, hq⟩ := h
  exact ⟨k, s', hs, hp, hQ _ hq⟩

theorem rr_bind {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop} (h : ReachesRet p ret s Q)
    (hQ : ∀ S, Q S → ReachesRet p ret S Q') : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hp, hq⟩ := h
  obtain ⟨k2, s2, hs2, hp2, hq2⟩ := hQ _ hq
  exact ⟨k + k2, s2, hs.trans hs2, hp2, hq2⟩

theorem bv_toNat_ofNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `EXTR #32, lo, hi` (the 64 bits at bit 32 of `hi:lo`) with `hi < 2^32`. -/
theorem extr32 (hi lo : BitVec 64) (h : hi.toNat < 2 ^ 32) :
    (BitVec.extractLsb' 32 64 (hi ++ lo)).toNat = hi.toNat * 2 ^ 32 + lo.toNat / 2 ^ 32 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have hl := lo.isLt
  have : (hi.toNat <<< 64 ||| lo.toNat) = hi.toNat * 2 ^ 64 + lo.toNat := by
    rw [Nat.shiftLeft_eq]; rw [Fv256.Util.or_hi_comm lo.toNat hi.toNat 64 (by simpa using hl)]; omega
  rw [this]
  have e : (hi.toNat * 18446744073709551616 + lo.toNat) / 4294967296 = hi.toNat * 4294967296 + lo.toNat / 4294967296 := by
    omega
  rw [e]
  apply Nat.mod_eq_of_lt
  have := lo.isLt
  omega


abbrev d64 : Nat := segAddr Extracted.program "math/bits.Div64"
abbrev head1 : Nat := d64 + 0x84
abbrev exit1 : Nat := d64 + 0xb0
abbrev head2 : Nat := d64 + 0xc4
abbrev exit2 : Nat := d64 + 0xec

theorem d64_lt : d64 + 0x100 < 2 ^ 47 := by decide

theorem lsr_ubfm (u : BitVec 64) (k : Nat) (hk : k < 64) :
    (u.rotateRight k &&& 18446744073709551615#64 &&& BitVec.ofNat 64 (2 ^ (64 - k) - 1)) = u >>> k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have : (BitVec.ofNat 64 (2 ^ (64 - k) - 1)).getLsbD i = decide (i < 64 - k) := by
    rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]; simp [hi]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_ushiftRight, this,
    show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes, hi]
  by_cases h : i < 64 - k
  · simp [h, Nat.mod_eq_of_lt hk]
  · simp [h]; apply BitVec.getLsbD_of_ge; omega


theorem ite_val (b : BitVec 64) (c : Nat) (hc : c ≤ 63) :
    (if 18446744073709551552 - c - 18446744073709551488 < 64 then
        b >>> ((18446744073709551552 - c - 18446744073709551488) % 64) else 0#64).toNat = b.toNat / 2 ^ (64 - c) := by
  by_cases h0 : c = 0
  · subst h0
    simp only [Nat.sub_zero]
    rw [if_neg (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.pow_zero]
    have := b.isLt
    simp
    exact (Nat.div_eq_of_lt (by simpa using this)).symm
  · have e : 18446744073709551552 - c - 18446744073709551488 = 64 - c := by omega
    rw [e, if_pos (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem un32_val (a b : BitVec 64) (c : Nat) (hc : c ≤ 63) (h : a.toNat * 2 ^ c < 2 ^ 64) :
    (a <<< c ||| if 18446744073709551552 - c - 18446744073709551488 < 64 then
        b >>> ((18446744073709551552 - c - 18446744073709551488) % 64) else 0#64).toNat =
      a.toNat * 2 ^ c + b.toNat / 2 ^ (64 - c) := by
  rw [BitVec.toNat_or, ite_val b c hc, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]
  have hb : b.toNat / 2 ^ (64 - c) < 2 ^ c := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    have := b.isLt
    rwa [show 64 - c + c = 64 by omega]
  rw [Fv256.Util.or_hi_comm _ _ _ hb]; omega

theorem un32_nat (a b : BitVec 64) (c : Nat) (hc : c ≤ 63) (h : a.toNat * 2 ^ c < 2 ^ 64) :
    (2 ^ c * a.toNat % 18446744073709551616 ||| (if 18446744073709551552 - c - 18446744073709551488 < 64 then
        b >>> ((18446744073709551552 - c - 18446744073709551488) % 64) else 0#64).toNat) =
      a.toNat * 2 ^ c + b.toNat / 2 ^ (64 - c) := by
  rw [← un32_val a b c hc h, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm (2 ^ c)]


theorem extr32g (hi lo : BitVec 64) :
    (BitVec.extractLsb' 32 64 (hi ++ lo)).toNat = (hi.toNat * 2 ^ 32 + lo.toNat / 2 ^ 32) % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have hl := lo.isLt
  have : (hi.toNat <<< 64 ||| lo.toNat) = hi.toNat * 2 ^ 64 + lo.toNat := by
    rw [Nat.shiftLeft_eq]; rw [Fv256.Util.or_hi_comm lo.toNat hi.toNat 64 (by simpa using hl)]; omega
  rw [this]
  have e : (hi.toNat * 18446744073709551616 + lo.toNat) / 4294967296 = hi.toNat * 4294967296 + lo.toNat / 4294967296 := by
    omega
  rw [e]
set_option maxHeartbeats 8000000 in
theorem loop1 (s0 : State) (ret : W64) (Q : State → Prop) (d1 d0 un10 A : Nat) (hd1 : 2 ^ 31 ≤ d1) (hd1' : d1 < 2 ^ 32)
    (hd0 : d0 < 2 ^ 32) (hun : un10 < 2 ^ 64) (hA : A < d1 * 2 ^ 32 + d0) (R0 : Nat → W64)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags), R' 6 = BitVec.ofNat 64 ((A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0)) →
      R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [6, 9, 10, 11, 12] → R' i = R0 i) →
      ReachesRet Extracted.program ret { s0 with regs := R', pc := BitVec.ofNat 64 exit1, flags := fl' } Q) :
    ∀ k q rhat (R : Nat → W64) (fl : Flags),
      q ≤ k → q * d1 + rhat = A → rhat < 2 ^ 32 →
      (A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0) ≤ q → q ≤ 2 ^ 32 + 1 →
      R 6 = BitVec.ofNat 64 q → R 9 = BitVec.ofNat 64 rhat → R 2 = BitVec.ofNat 64 (d1 * 2 ^ 32 + d0) →
      R 8 = BitVec.ofNat 64 d0 → R 7 = BitVec.ofNat 64 un10 → (∀ i, i ∉ [6, 9, 10, 11, 12] → R i = R0 i) →
      ReachesRet Extracted.program ret { s0 with regs := R, pc := BitVec.ofNat 64 head1, flags := fl } Q := by
  have hcode := d64_lt
  janus_eval_nat hh1 : head1
  janus_eval_nat hh2 : exit1
  simp only [hh1, hh2] at hK ⊢
  have hy0 : 0 < d1 * 2 ^ 32 + d0 := by omega
  have sg : ∀ q rhat, q * d1 + rhat = A → (2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un10 / 2 ^ 32 < q * d0) →
      (A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0) < q := fun q rhat hI hc =>
    Fv256.D64.step_gt (2 ^ 32) d1 d0 A (un10 / 2 ^ 32) q rhat (by omega) hA hI hc
  generalize hNq : (A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0) = Nq at sg hK ⊢
  have ee : ∀ q rhat, q * d1 + rhat = A → Nq ≤ q → q * d0 ≤ 2 ^ 32 * rhat + un10 / 2 ^ 32 → q = Nq := by
    intro q rhat hI hge hc
    have := Fv256.D64.exit_eq (2 ^ 32) d1 d0 A (un10 / 2 ^ 32) q rhat hI (by rw [hNq]; exact hge) hc hy0
    rw [hNq] at this; exact this
  have eb : ∀ q rhat, q * d1 + rhat = A → Nq ≤ q → 2 ^ 32 ≤ rhat → q ≤ 2 ^ 32 → q = Nq := by
    intro q rhat hI hge hr hq
    have := Fv256.D64.exit_break (2 ^ 32) d1 d0 A (un10 / 2 ^ 32) q rhat hI (by rw [hNq]; exact hge) hr hq hd0 hy0
    rw [hNq] at this; exact this
  intro k
  induction k with
  | zero =>
    intro q rhat R fl hk hI hr hge hq h6 h9 h2 h8 h7 hRu
    have e6 : (R 6).toNat = q := by rw [h6]; exact bv_toNat_ofNat_lt _ (by omega)
    have e9 : (R 9).toNat = rhat := by rw [h9]; exact bv_toNat_ofNat_lt _ (by omega)
    have e8 : (R 8).toNat = d0 := by rw [h8]; exact bv_toNat_ofNat_lt _ (by omega)
    have e7 : (R 7).toNat = un10 := by rw [h7]; exact bv_toNat_ofNat_lt _ (by omega)
    have eX := extr32 (R 9) (R 7) (by omega)
    rw [e9, e7] at eX
    have hq0 : q = 0 := by omega
    subst hq0
    janus_run until [d64 + 0x84, d64 + 0xb0]
    · have hm : (R 6 * R 8).toNat = 0 := by rw [BitVec.toNat_mul, e6]; simp
      refine hK _ _ ?_ ?_ ?_
      · have := ee 0 rhat hI hge (by omega)
        simp [setReg, ← this, h6]
      · simp [setReg]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [setReg]
        grind
    · exfalso; rw [BitVec.toNat_mul, e6] at *; simp at *; try omega
    · exfalso; rw [BitVec.toNat_mul, e6] at *; simp at *; try omega
  | succ k ih =>
    intro q rhat R fl hk hI hr hge hq h6 h9 h2 h8 h7 hRu
    have e6 : (R 6).toNat = q := by rw [h6]; exact bv_toNat_ofNat_lt _ (by omega)
    have e9 : (R 9).toNat = rhat := by rw [h9]; exact bv_toNat_ofNat_lt _ (by omega)
    have e8 : (R 8).toNat = d0 := by rw [h8]; exact bv_toNat_ofNat_lt _ (by omega)
    have e7 : (R 7).toNat = un10 := by rw [h7]; exact bv_toNat_ofNat_lt _ (by omega)
    have e2 : (R 2 >>> 32).toNat = d1 := by
      rw [BitVec.toNat_ushiftRight, h2, bv_toNat_ofNat_lt _ (by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have eX := extr32 (R 9) (R 7) (by omega)
    rw [e9, e7] at eX
    have hLoop' : Nq < q → rhat + d1 < 2 ^ 32 → ∀ (RR : Nat → W64) fl', RR 6 = R 6 - 1#64 → RR 9 = R 9 + R 2 >>> 32 →
        RR 10 = 4294967296#64 → (∀ i, i ∉ [6, 9, 10, 11, 12] → RR i = R i) →
        ReachesRet Extracted.program ret { s0 with regs := RR, pc := 576356#64, flags := fl' } Q := by
      intro hgt hrr RR fl' r6 r9 r10 rr
      have hq1 : 1 ≤ q := by omega
      refine ih (q - 1) (rhat + d1) RR fl' (by omega) ?_ hrr (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_
      · cases q with
        | zero => omega
        | succ q => simp only [Nat.add_sub_cancel]; rw [← hI]; grind
      · rw [r6, h6]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, bv_toNat_ofNat_lt _ (by omega)]
        simp; omega
      · rw [r9]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, e9, e2, bv_toNat_ofNat_lt _ (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [rr 2 (by simp), h2]
      · rw [rr 8 (by simp), h8]
      · rw [rr 7 (by simp), h7]
      · intro i hi
        rw [rr i hi]; exact hRu i hi
    have hBrk : Nq < q → 2 ^ 32 ≤ rhat + d1 → ∀ (RR : Nat → W64) fl', RR 6 = R 6 - 1#64 → RR 10 = 4294967296#64 →
        (∀ i, i ∉ [6, 9, 10, 11, 12] → RR i = R i) →
        ReachesRet Extracted.program ret { s0 with regs := RR, pc := 576400#64, flags := fl' } Q := by
      intro hgt hrr RR fl' r6 r10 rr
      have hq1 : 1 ≤ q := by omega
      refine hK _ _ ?_ ?_ ?_
      · have hI' : (q - 1) * d1 + (rhat + d1) = A := by
          cases q with
          | zero => omega
          | succ q => simp only [Nat.add_sub_cancel]; rw [← hI]; grind
        have := eb (q - 1) (rhat + d1) hI' (by omega) hrr (by omega)
        rw [← this, r6, h6]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, bv_toNat_ofNat_lt _ (by omega)]
        simp; omega
      · rw [r10]
      · intro i hi
        rw [rr i hi]; exact hRu i hi
    have hm : ¬ 4294967296 ≤ (R 6).toNat → (R 6 * R 8).toNat = q * d0 := by
      intro hlt
      rw [BitVec.toNat_mul, e6, e8]; apply Nat.mod_eq_of_lt
      calc q * d0 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]
    janus_run until [d64 + 0x84, d64 + 0xb0]
    · exact hLoop' (sg q rhat hI (Or.inl (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · exact hBrk (sg q rhat hI (Or.inl (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · have hm' := hm (by omega)
      refine hK _ _ ?_ ?_ ?_
      · have := ee q rhat hI hge (by omega)
        simp [setReg, ← this, h6]
      · simp [setReg]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [setReg]
        grind
    · have hm' := hm (by omega)
      exact hLoop' (sg q rhat hI (Or.inr (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · have hm' := hm (by omega)
      exact hBrk (sg q rhat hI (Or.inr (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)

set_option maxHeartbeats 8000000 in
theorem loop2 (s0 : State) (ret : W64) (Q : State → Prop) (d1 d0 un0 A : Nat) (hd1 : 2 ^ 31 ≤ d1) (hd1' : d1 < 2 ^ 32)
    (hd0 : d0 < 2 ^ 32) (hun : un0 < 2 ^ 32) (hA : A < d1 * 2 ^ 32 + d0) (R0 : Nat → W64)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags), R' 9 = BitVec.ofNat 64 ((A * 2 ^ 32 + un0) / (d1 * 2 ^ 32 + d0)) →
      R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [5, 9, 11, 12] → R' i = R0 i) →
      ReachesRet Extracted.program ret { s0 with regs := R', pc := BitVec.ofNat 64 exit2, flags := fl' } Q) :
    ∀ k q rhat (R : Nat → W64) (fl : Flags),
      q ≤ k → q * d1 + rhat = A → rhat < 2 ^ 32 →
      (A * 2 ^ 32 + un0) / (d1 * 2 ^ 32 + d0) ≤ q → q ≤ 2 ^ 32 + 1 →
      R 9 = BitVec.ofNat 64 q → R 5 = BitVec.ofNat 64 rhat → R 2 = BitVec.ofNat 64 (d1 * 2 ^ 32 + d0) →
      R 8 = BitVec.ofNat 64 d0 → R 7 = BitVec.ofNat 64 un0 → R 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [5, 9, 11, 12] → R i = R0 i) →
      ReachesRet Extracted.program ret { s0 with regs := R, pc := BitVec.ofNat 64 head2, flags := fl } Q := by
  have hcode := d64_lt
  janus_eval_nat hh1 : head2
  janus_eval_nat hh2 : exit2
  simp only [hh1, hh2] at hK ⊢
  have hy0 : 0 < d1 * 2 ^ 32 + d0 := by omega
  have sg : ∀ q rhat, q * d1 + rhat = A → (2 ^ 32 ≤ q ∨ 2 ^ 32 * rhat + un0 < q * d0) →
      (A * 2 ^ 32 + un0) / (d1 * 2 ^ 32 + d0) < q := fun q rhat hI hc =>
    Fv256.D64.step_gt (2 ^ 32) d1 d0 A (un0) q rhat (by omega) hA hI hc
  generalize hNq : (A * 2 ^ 32 + un0) / (d1 * 2 ^ 32 + d0) = Nq at sg hK ⊢
  have ee : ∀ q rhat, q * d1 + rhat = A → Nq ≤ q → q * d0 ≤ 2 ^ 32 * rhat + un0 → q = Nq := by
    intro q rhat hI hge hc
    have := Fv256.D64.exit_eq (2 ^ 32) d1 d0 A (un0) q rhat hI (by rw [hNq]; exact hge) hc hy0
    rw [hNq] at this; exact this
  have eb : ∀ q rhat, q * d1 + rhat = A → Nq ≤ q → 2 ^ 32 ≤ rhat → q ≤ 2 ^ 32 → q = Nq := by
    intro q rhat hI hge hr hq
    have := Fv256.D64.exit_break (2 ^ 32) d1 d0 A (un0) q rhat hI (by rw [hNq]; exact hge) hr hq hd0 hy0
    rw [hNq] at this; exact this
  intro k
  induction k with
  | zero =>
    intro q rhat R fl hk hI hr hge hq h6 h9 h2 h8 h7 h10 hRu
    have e6 : (R 9).toNat = q := by rw [h6]; exact bv_toNat_ofNat_lt _ (by omega)
    have e9 : (R 5).toNat = rhat := by rw [h9]; exact bv_toNat_ofNat_lt _ (by omega)
    have e8 : (R 8).toNat = d0 := by rw [h8]; exact bv_toNat_ofNat_lt _ (by omega)
    have e7 : (R 7).toNat = un0 := by rw [h7]; exact bv_toNat_ofNat_lt _ (by omega)
    have e2 : (R 2 >>> 32).toNat = d1 := by
      rw [BitVec.toNat_ushiftRight, h2, bv_toNat_ofNat_lt _ (by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have e10 : (R 10).toNat = 2 ^ 32 := by rw [h10]; exact bv_toNat_ofNat_lt _ (by omega)
    have eX : ((R 7).toNat + 4294967296 * (R 5).toNat) % 18446744073709551616 = un0 + 4294967296 * rhat := by
      rw [e7, e9]; exact Nat.mod_eq_of_lt (by omega)
    have eY : ((R 5).toNat + (R 2 >>> 32).toNat) % 18446744073709551616 = rhat + d1 := by
      rw [e9, e2]; exact Nat.mod_eq_of_lt (by omega)
    have hq0 : q = 0 := by omega
    subst hq0
    janus_run until [d64 + 0xc4, d64 + 0xec]
    · have hm : (R 9 * R 8).toNat = 0 := by rw [BitVec.toNat_mul, e6]; simp
      refine hK _ _ ?_ ?_ ?_
      · have := ee 0 rhat hI hge (by omega)
        simp [setReg, ← this, h6]
      · simp [setReg, h10]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [setReg]
        grind
    · exfalso; rw [BitVec.toNat_mul, e6] at *; simp at *; try omega
    · exfalso; rw [BitVec.toNat_mul, e6] at *; simp at *; try omega
  | succ k ih =>
    intro q rhat R fl hk hI hr hge hq h6 h9 h2 h8 h7 h10 hRu
    have e6 : (R 9).toNat = q := by rw [h6]; exact bv_toNat_ofNat_lt _ (by omega)
    have e9 : (R 5).toNat = rhat := by rw [h9]; exact bv_toNat_ofNat_lt _ (by omega)
    have e8 : (R 8).toNat = d0 := by rw [h8]; exact bv_toNat_ofNat_lt _ (by omega)
    have e7 : (R 7).toNat = un0 := by rw [h7]; exact bv_toNat_ofNat_lt _ (by omega)
    have e2 : (R 2 >>> 32).toNat = d1 := by
      rw [BitVec.toNat_ushiftRight, h2, bv_toNat_ofNat_lt _ (by omega), Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    have e10 : (R 10).toNat = 2 ^ 32 := by rw [h10]; exact bv_toNat_ofNat_lt _ (by omega)
    have eX : ((R 7).toNat + 4294967296 * (R 5).toNat) % 18446744073709551616 = un0 + 4294967296 * rhat := by
      rw [e7, e9]; exact Nat.mod_eq_of_lt (by omega)
    have eY : ((R 5).toNat + (R 2 >>> 32).toNat) % 18446744073709551616 = rhat + d1 := by
      rw [e9, e2]; exact Nat.mod_eq_of_lt (by omega)
    have hLoop' : Nq < q → rhat + d1 < 2 ^ 32 → ∀ (RR : Nat → W64) fl', RR 9 = R 9 - 1#64 → RR 5 = R 5 + R 2 >>> 32 →
        (∀ i, i ∉ [5, 9, 11, 12] → RR i = R i) →
        ReachesRet Extracted.program ret { s0 with regs := RR, pc := 576420#64, flags := fl' } Q := by
      intro hgt hrr RR fl' r6 r9 rr
      have hq1 : 1 ≤ q := by omega
      refine ih (q - 1) (rhat + d1) RR fl' (by omega) ?_ hrr (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · cases q with
        | zero => omega
        | succ q => simp only [Nat.add_sub_cancel]; rw [← hI]; grind
      · rw [r6, h6]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, bv_toNat_ofNat_lt _ (by omega)]
        simp; omega
      · rw [r9]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, e9, e2, bv_toNat_ofNat_lt _ (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      · rw [rr 2 (by simp), h2]
      · rw [rr 8 (by simp), h8]
      · rw [rr 7 (by simp), h7]
      · rw [rr 10 (by simp), h10]
      · intro i hi
        rw [rr i hi]; exact hRu i hi
    have hBrk : Nq < q → 2 ^ 32 ≤ rhat + d1 → ∀ (RR : Nat → W64) fl', RR 9 = R 9 - 1#64 →
        (∀ i, i ∉ [5, 9, 11, 12] → RR i = R i) →
        ReachesRet Extracted.program ret { s0 with regs := RR, pc := 576460#64, flags := fl' } Q := by
      intro hgt hrr RR fl' r6 rr
      have hq1 : 1 ≤ q := by omega
      refine hK _ _ ?_ ?_ ?_
      · have hI' : (q - 1) * d1 + (rhat + d1) = A := by
          cases q with
          | zero => omega
          | succ q => simp only [Nat.add_sub_cancel]; rw [← hI]; grind
        have := eb (q - 1) (rhat + d1) hI' (by omega) hrr (by omega)
        rw [← this, r6, h6]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, bv_toNat_ofNat_lt _ (by omega)]
        simp; omega
      · rw [rr 10 (by simp), h10]
      · intro i hi
        rw [rr i hi]; exact hRu i hi
    have hm : ¬ 4294967296 ≤ (R 9).toNat → (R 9 * R 8).toNat = q * d0 := by
      intro hlt
      rw [BitVec.toNat_mul, e6, e8]; apply Nat.mod_eq_of_lt
      calc q * d0 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_le_of_lt (by omega) (by omega) (by omega)
        _ = 2 ^ 64 := by rw [← Nat.pow_add]
    janus_run until [d64 + 0xc4, d64 + 0xec]
    · exact hLoop' (sg q rhat hI (Or.inl (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · exact hBrk (sg q rhat hI (Or.inl (by omega))) (by omega) _ _ (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · have hm' := hm (by omega)
      refine hK _ _ ?_ ?_ ?_
      · have := ee q rhat hI hge (by omega)
        simp [setReg, ← this, h6]
      · simp [setReg, h10]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        simp [setReg]
        grind
    · have hm' := hm (by omega)
      exact hLoop' (sg q rhat hI (Or.inr (by omega))) (by omega) _ _ (by simp [setReg]) (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)
    · have hm' := hm (by omega)
      exact hBrk (sg q rhat hI (Or.inr (by omega))) (by omega) _ _ (by simp [setReg]) (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi; simp [setReg]; grind)


theorem loop1e (s0 : State) (ret : W64) (Q : State → Prop) (d1 d0 un10 A : Nat) (hd1 : 2 ^ 31 ≤ d1) (hd1' : d1 < 2 ^ 32)
    (hd0 : d0 < 2 ^ 32) (hun : un10 < 2 ^ 64) (hA : A < d1 * 2 ^ 32 + d0) (R : Nat → W64) (fl : Flags)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags), R' 6 = BitVec.ofNat 64 ((A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0)) →
      R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [6, 9, 10, 11, 12] → R' i = R i) →
      ReachesRet Extracted.program ret { s0 with regs := R', pc := 576400#64, flags := fl' } Q)
    (q rhat : Nat) (hI : q * d1 + rhat = A) (hr : rhat < 2 ^ 32)
    (hge : (A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0) ≤ q) (hq : q ≤ 2 ^ 32 + 1)
    (h6 : R 6 = BitVec.ofNat 64 q) (h9 : R 9 = BitVec.ofNat 64 rhat) (h2 : R 2 = BitVec.ofNat 64 (d1 * 2 ^ 32 + d0))
    (h8 : R 8 = BitVec.ofNat 64 d0) (h7 : R 7 = BitVec.ofNat 64 un10) :
    ReachesRet Extracted.program ret { s0 with regs := R, pc := 576356#64, flags := fl } Q := by
  janus_eval_nat hh1 : head1
  janus_eval_nat hh2 : exit1
  have hK' : ∀ (R' : Nat → W64) (fl' : Flags), R' 6 = BitVec.ofNat 64 ((A * 2 ^ 32 + un10 / 2 ^ 32) / (d1 * 2 ^ 32 + d0)) → R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [6, 9, 10, 11, 12] → R' i = R i) → ReachesRet Extracted.program ret { s0 with regs := R', pc := BitVec.ofNat 64 exit1, flags := fl' } Q := by
    intro R' fl' a b c
    have := hK R' fl' a b c
    simp only [hh2] at this ⊢
    exact this
  have := loop1 s0 ret Q d1 d0 un10 A hd1 hd1' hd0 hun hA R hK' q q rhat R fl (Nat.le_refl _) hI hr hge hq h6 h9 h2 h8 h7 (fun _ _ => rfl)
  simp only [hh1] at this
  exact this

theorem loop2e (s0 : State) (ret : W64) (Q : State → Prop) (d1 d0 un10 A : Nat) (hd1 : 2 ^ 31 ≤ d1) (hd1' : d1 < 2 ^ 32)
    (hd0 : d0 < 2 ^ 32) (hun : un10 < 2 ^ 32) (hA : A < d1 * 2 ^ 32 + d0) (R : Nat → W64) (fl : Flags)
    (hK : ∀ (R' : Nat → W64) (fl' : Flags), R' 9 = BitVec.ofNat 64 ((A * 2 ^ 32 + un10) / (d1 * 2 ^ 32 + d0)) →
      R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [5, 9, 11, 12] → R' i = R i) →
      ReachesRet Extracted.program ret { s0 with regs := R', pc := 576460#64, flags := fl' } Q)
    (q rhat : Nat) (hI : q * d1 + rhat = A) (hr : rhat < 2 ^ 32)
    (hge : (A * 2 ^ 32 + un10) / (d1 * 2 ^ 32 + d0) ≤ q) (hq : q ≤ 2 ^ 32 + 1)
    (h6 : R 9 = BitVec.ofNat 64 q) (h9 : R 5 = BitVec.ofNat 64 rhat) (h2 : R 2 = BitVec.ofNat 64 (d1 * 2 ^ 32 + d0))
    (h8 : R 8 = BitVec.ofNat 64 d0) (h7 : R 7 = BitVec.ofNat 64 un10) (h10 : R 10 = BitVec.ofNat 64 (2 ^ 32)) :
    ReachesRet Extracted.program ret { s0 with regs := R, pc := 576420#64, flags := fl } Q := by
  janus_eval_nat hh1 : head2
  janus_eval_nat hh2 : exit2
  have hK' : ∀ (R' : Nat → W64) (fl' : Flags), R' 9 = BitVec.ofNat 64 ((A * 2 ^ 32 + un10) / (d1 * 2 ^ 32 + d0)) → R' 10 = BitVec.ofNat 64 (2 ^ 32) → (∀ i, i ∉ [5, 9, 11, 12] → R' i = R i) → ReachesRet Extracted.program ret { s0 with regs := R', pc := BitVec.ofNat 64 exit2, flags := fl' } Q := by
    intro R' fl' a b c
    have := hK R' fl' a b c
    simp only [hh2] at this ⊢
    exact this
  have := loop2 s0 ret Q d1 d0 un10 A hd1 hd1' hd0 hun hA R hK' q q rhat R fl (Nat.le_refl _) hI hr hge hq h6 h9 h2 h8 h7 h10 (fun _ _ => rfl)
  simp only [hh1] at this
  exact this

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem div64_summary :
    Summary Extracted.program d64
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 0 ∧ StackOK s 40 0 ∧
        (s.regs 2).toNat ≠ 0 ∧ (s.regs 0).toNat < (s.regs 2).toNat)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        (s'.regs 0).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat ∧
        (s'.regs 1).toNat = ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) % (s.regs 2).toNat ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16] → s'.regs i = s.regs i) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 40, s.sp.toNat - 24)]) := by
  intro s hpc ⟨h30a, h30b, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hy, hhi⟩
  have hcode := d64_lt
  janus_run until [d64 + 0x5c]
  · have hm := Nat.mul_comm (s.regs 2).toNat ((s.regs 1).toNat / (s.regs 2).toNat)
    have hdm := Nat.div_add_mod (s.regs 1).toNat (s.regs 2).toNat
    have hl := (s.regs 1).isLt
    have hq : (s.regs 1).toNat / (s.regs 2).toNat * (s.regs 2).toNat ≤ (s.regs 1).toNat := Nat.div_mul_le_self _ _
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.mod_eq_of_lt (by omega : (s.regs 1).toNat / (s.regs 2).toNat * (s.regs 2).toNat < 2 ^ 64)]
      omega
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · janus_frame
  · obtain ⟨hc63, hc1, hc2⟩ := Fv256.B.clz_norm (s.regs 2).toNat hy (s.regs 2).isLt
    generalize clzNat 64 (s.regs 2).toNat = c at *
    have hsh : c % 18446744073709551616 % 64 = c := by omega
    have e5 : ((s.regs 2 <<< c).rotateRight 32 &&& 18446744073709551615#64 &&& 4294967295#64) = (s.regs 2 <<< c) >>> 32 := lsr_ubfm _ 32 (by decide)
    have hy' : (s.regs 2 <<< c).toNat = (s.regs 2).toNat * 2 ^ c := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hc2]
    have hnz : ¬ ((s.regs 2 <<< c) >>> 32 = 0#64) := by
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hy'] at this
      simp at this
      omega
    rw [hsh] at *
    janus_run [e5, hnz] until [d64 + 0x84]
    have hhc : (s.regs 0).toNat * 2 ^ c < 2 ^ 64 := by
      have : (s.regs 0).toNat + 1 ≤ (s.regs 2).toNat := hhi
      have := Nat.mul_le_mul_right (2 ^ c) this
      rw [Nat.add_mul] at this
      omega
    have hU4 := un32_val (s.regs 0) (s.regs 1) c hc63 hhc
    have hU4n := un32_nat (s.regs 0) (s.regs 1) c hc63 hhc
    have hU7 : (s.regs 1 <<< c).toNat = (s.regs 1).toNat * 2 ^ c % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    rw [hU4n]
    generalize hY : s.regs 2 <<< c = Y at *
    generalize hU4e : (s.regs 0 <<< c ||| if 18446744073709551552 - c - 18446744073709551488 < 64 then
          s.regs 1 >>> ((18446744073709551552 - c - 18446744073709551488) % 64) else 0#64) = U4 at *
    generalize hU7e : s.regs 1 <<< c = U7 at *
    generalize hAe : (s.regs 0).toNat * 2 ^ c + (s.regs 1).toNat / 2 ^ (64 - c) = A at *
    have hY1 : (Y >>> 32).toNat = Y.toNat / 2 ^ 32 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hY0 : (Y &&& 4294967295#64).toNat = Y.toNat % 2 ^ 32 := by
      rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
    obtain ⟨d1, hd1def⟩ : ∃ d1, d1 = Y.toNat / 2 ^ 32 := ⟨_, rfl⟩
    obtain ⟨d0, hd0def⟩ : ∃ d0, d0 = Y.toNat % 2 ^ 32 := ⟨_, rfl⟩
    have hYd : Y.toNat = d1 * 2 ^ 32 + d0 := by omega
    have hd1l : 2 ^ 31 ≤ d1 := by omega
    have hd1u : d1 < 2 ^ 32 := by have := Y.isLt; omega
    have hd0u : d0 < 2 ^ 32 := by omega
    have hY1' : (Y >>> 32).toNat = d1 := by rw [hY1, hd1def]
    have hY0' : (Y &&& 4294967295#64).toNat = d0 := by rw [hY0, hd0def]
    have hYo : Y = BitVec.ofNat 64 (d1 * 2 ^ 32 + d0) := by
      rw [← hYd]; exact (BitVec.ofNat_toNat 64 Y).symm.trans (by simp)
    have hAlt : A < d1 * 2 ^ 32 + d0 := by
      rw [← hYd, hy', ← hAe]
      have h1 : (s.regs 0).toNat + 1 ≤ (s.regs 2).toNat := hhi
      have h2 := Nat.mul_le_mul_right (2 ^ c) h1
      rw [Nat.add_mul] at h2
      have h3 : (s.regs 1).toNat / 2 ^ (64 - c) < 2 ^ c := by
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add]
        have := (s.regs 1).isLt
        rwa [show 64 - c + c = 64 by omega]
      omega
    have hd1p : 0 < d1 := by omega
    have hIq : A / d1 * d1 + A % d1 = A := by have := Nat.div_add_mod A d1; rw [Nat.mul_comm] at this; omega
    have hrq : A % d1 < 2 ^ 32 := by have := Nat.mod_lt A hd1p; omega
    have hqb : A / d1 ≤ 2 ^ 32 + 1 := Fv256.D64.init_bound (2 ^ 32) d1 d0 A (by omega) hd0u hAlt
    have hgeq : (A * 2 ^ 32 + U7.toNat / 2 ^ 32) / (d1 * 2 ^ 32 + d0) ≤ A / d1 :=
      Fv256.D64.est_ge (2 ^ 32) d1 d0 A (U7.toNat / 2 ^ 32) (by omega) (by have := U7.isLt; omega) hd1p
    refine loop1e { s with sp := s.sp - 32#64, mem := (s.mem.writeLE (BitVec.toNat s.sp - 32) 8 (BitVec.toNat (s.regs 30))).writeLE (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29)) } (s.regs regLR) _ d1 d0 U7.toNat A hd1l hd1u hd0u U7.isLt hAlt _ _ ?hK (A / d1) (A % d1) hIq hrq hgeq hqb ?_ ?_ ?_ ?_ ?_
    case hK =>
      intro R' fl' h6 h10 hu
      have r2 : R' 2 = Y := by rw [hu 2 (by simp)]; simp [setReg]
      have r3 : R' 3 = BitVec.ofNat 64 c := by rw [hu 3 (by simp)]; simp [setReg]
      have r4 : R' 4 = U4 := by rw [hu 4 (by simp)]; simp [setReg]
      have r5 : R' 5 = Y >>> 32 := by rw [hu 5 (by simp)]; simp [setReg]
      have r7 : R' 7 = U7 := by rw [hu 7 (by simp)]; simp [setReg]
      have r8 : R' 8 = Y &&& 4294967295#64 := by rw [hu 8 (by simp)]; simp [setReg]
      obtain ⟨Nq1, hNq1⟩ : ∃ n, n = (A * 2 ^ 32 + U7.toNat / 2 ^ 32) / (d1 * 2 ^ 32 + d0) := ⟨_, rfl⟩
      rw [← hNq1] at h6
      have hNq1b : Nq1 ≤ A / d1 := hNq1 ▸ hgeq
      have hP : Nq1 * (d1 * 2 ^ 32 + d0) ≤ A * 2 ^ 32 + U7.toNat / 2 ^ 32 := by rw [hNq1]; exact Nat.div_mul_le_self _ _
      have hu21 : A * 2 ^ 32 + U7.toNat / 2 ^ 32 - Nq1 * (d1 * 2 ^ 32 + d0) < d1 * 2 ^ 32 + d0 := by
        rw [hNq1]; exact Fv256.D64.rem_lt _ _ (by omega)
      obtain ⟨un21, hun21⟩ : ∃ n, n = A * 2 ^ 32 + U7.toNat / 2 ^ 32 - Nq1 * (d1 * 2 ^ 32 + d0) := ⟨_, rfl⟩
      rw [← hun21] at hu21
      have hNq1c := hNq1
      have hun21c := hun21
      have hext : (BitVec.extractLsb' 32 64 (U4 ++ U7)).toNat = (A * 2 ^ 32 + U7.toNat / 2 ^ 32) % 2 ^ 64 := by
        rw [extr32g, hU4]
      have hYm : (Y * BitVec.ofNat 64 Nq1).toNat = (d1 * 2 ^ 32 + d0) * Nq1 % 2 ^ 64 := by
        have : Nq1 < 2 ^ 64 := by have := hqb; omega
        rw [BitVec.toNat_mul, bv_toNat_ofNat_lt _ this, hYd]
      have hnat : (2 ^ 64 - (Y * BitVec.ofNat 64 Nq1).toNat + (BitVec.extractLsb' 32 64 (U4 ++ U7)).toNat) % 2 ^ 64 = un21 := by
        rw [hYm, hext]
        have hm := Nat.mul_comm (d1 * 2 ^ 32 + d0) Nq1
        have : un21 < 2 ^ 64 := by have := Y.isLt; omega
        omega
      have hR4 : BitVec.extractLsb' 32 64 (U4 ++ U7) - Y * BitVec.ofNat 64 Nq1 = BitVec.ofNat 64 un21 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, hnat, bv_toNat_ofNat_lt _ (by have := Y.isLt; omega)]
      have hd1ne : (Y >>> 32).toNat ≠ 0 := by omega
      janus_run [r2, r3, r4, r5, r7, r8, h6] until [d64 + 0xc4]
      simp only [Nat.reducePow] at hNq1 hnat hP hu21 hun21
      simp only [hnat, hR4, hd1ne, if_false]
      rw [hY1']
      have hun0 : (U7 &&& 4294967295#64).toNat = U7.toNat % 2 ^ 32 := by
        rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 32
      have hu21b : un21 < d1 * 2 ^ 32 + d0 := hu21
      have hIq2 : un21 / d1 * d1 + un21 % d1 = un21 := by have := Nat.div_add_mod un21 d1; rw [Nat.mul_comm] at this; omega
      have hrq2 : un21 % d1 < 2 ^ 32 := by have := Nat.mod_lt un21 hd1p; omega
      have hqb2 : un21 / d1 ≤ 2 ^ 32 + 1 := Fv256.D64.init_bound (2 ^ 32) d1 d0 un21 (by omega) hd0u hu21b
      have hgeq2 : (un21 * 2 ^ 32 + U7.toNat % 2 ^ 32) / (d1 * 2 ^ 32 + d0) ≤ un21 / d1 :=
        Fv256.D64.est_ge (2 ^ 32) d1 d0 un21 (U7.toNat % 2 ^ 32) (by omega) (by omega) hd1p
      refine loop2e { s with sp := s.sp - 32#64, mem := (s.mem.writeLE (BitVec.toNat s.sp - 32) 8 (BitVec.toNat (s.regs 30))).writeLE (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29)) } (s.regs regLR) _ d1 d0 (U7.toNat % 2 ^ 32) un21 hd1l hd1u hd0u (by omega) hu21b _ _ ?hK2 (un21 / d1) (un21 % d1) hIq2 hrq2 hgeq2 hqb2 ?_ ?_ ?_ ?_ ?_ ?_
      case hK2 =>
        intro R'' fl'' h9' h10' hu2
        obtain ⟨Nq2, hNq2⟩ : ∃ n, n = (un21 * 2 ^ 32 + U7.toNat % 2 ^ 32) / (d1 * 2 ^ 32 + d0) := ⟨_, rfl⟩
        rw [← hNq2] at h9'
        have q2 : R'' 2 = Y := by rw [hu2 2 (by simp)]; simp [setReg, r2]
        have q3 : R'' 3 = BitVec.ofNat 64 c := by rw [hu2 3 (by simp)]; simp [setReg, r3]
        have q4 : R'' 4 = BitVec.ofNat 64 un21 := by rw [hu2 4 (by simp)]; simp [setReg]
        have q6 : R'' 6 = BitVec.ofNat 64 Nq1 := by rw [hu2 6 (by simp)]; simp [setReg, h6]
        have q7 : R'' 7 = U7 &&& 4294967295#64 := by rw [hu2 7 (by simp)]; simp [setReg]
        janus_run [q2, q3, q4, q6, q7, h9']
        have hy0' : 0 < (s.regs 2).toNat := by omega
        have hys : (s.regs 2).toNat * 2 ^ c < 2 ^ 64 := hc2
        have hNq1' : Nq1 = (A * 2 ^ 32 + U7.toNat / 2 ^ 32) / ((s.regs 2).toNat * 2 ^ c) := by
          rw [← hy', hYd]; exact hNq1c
        have hNq2' : Nq2 = (un21 * 2 ^ 32 + U7.toNat % 2 ^ 32) / ((s.regs 2).toNat * 2 ^ c) := by
          rw [← hy', hYd]; exact hNq2
        have hun21' : un21 = (A * 2 ^ 32 + U7.toNat / 2 ^ 32) - Nq1 * ((s.regs 2).toNat * 2 ^ c) := by
          rw [← hy', hYd]; exact hun21c
        obtain ⟨r0, hr0⟩ : ∃ r, r = (un21 * 2 ^ 32 + U7.toNat % 2 ^ 32) - Nq2 * ((s.regs 2).toNat * 2 ^ c) := ⟨_, rfl⟩
        have hasm := Fv256.D64.assemble (s.regs 0).toNat (s.regs 1).toNat (s.regs 2).toNat c hy0' hys hhi (by omega) Nq1 Nq2 un21 r0
          (A * 2 ^ 32 + U7.toNat / 2 ^ 32) (un21 * 2 ^ 32 + U7.toNat % 2 ^ 32) A U7.toNat hAe.symm hU7 rfl hNq1' hun21' rfl hNq2' hr0
        have hUlt : ((s.regs 0).toNat * 2 ^ 64 + (s.regs 1).toNat) / (s.regs 2).toNat < 2 ^ 64 := by
          apply Nat.div_lt_of_lt_mul
          have := (s.regs 1).isLt
          have h1 : (s.regs 0).toNat + 1 ≤ (s.regs 2).toNat := hhi
          have h2 := Nat.mul_le_mul_right (2 ^ 64) h1
          rw [Nat.add_mul] at h2
          rw [Nat.mul_comm]
          omega
        have hP2 : Nq2 * ((s.regs 2).toNat * 2 ^ c) ≤ un21 * 2 ^ 32 + U7.toNat % 2 ^ 32 := by
          rw [hNq2']; exact Nat.div_mul_le_self _ _
        have hr0lt : r0 < (s.regs 2).toNat * 2 ^ c := by
          rw [hr0, hNq2']; exact Fv256.D64.rem_lt _ _ (by omega)
        have hX : (U7 &&& 4294967295#64) + BitVec.ofNat 64 (un21 * 4294967296) - Y * BitVec.ofNat 64 Nq2 = BitVec.ofNat 64 r0 := by
          apply BitVec.eq_of_toNat_eq
          have hNq2l : Nq2 < 2 ^ 64 := by
            have h1 := hasm.1
            omega
          rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, hun0, bv_toNat_ofNat_lt _ hNq2l, hy', bv_toNat_ofNat_lt r0 (by omega), BitVec.toNat_ofNat]
          have hm := Nat.mul_comm ((s.regs 2).toNat * 2 ^ c) Nq2
          generalize (s.regs 2).toNat * 2 ^ c = Yn at hr0 hP2 hr0lt hm hys ⊢
          omega
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hu2 28 (by simp)]; simp [setReg, hu 28 (by simp)]
        · rw [hu2 18 (by simp)]; simp [setReg, hu 18 (by simp)]
        · have h1 := hasm.1
          have h2 := hUlt
          simp only [Nat.reducePow] at h1 h2
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · rw [hX, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, bv_toNat_ofNat_lt r0 (by omega), Nat.mod_eq_of_lt (by omega)]
          exact hasm.2
        · intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
          by_cases h30 : i = 30
          · subst h30; simp
          by_cases h29 : i = 29
          · subst h29; simp
          rw [if_neg h30, if_neg h29, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          rw [hu2 i (by simp; omega)]
          simp only [setReg]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          rw [hu i (by simp; omega)]
          simp only [setReg]
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · janus_frame
      · simp [setReg, hY1']
      · simp only [setReg]
        simp only [hY1', show (5 : Nat) ≠ 9 by decide, show (5 : Nat) ≠ 7 by decide, show (5 : Nat) ≠ 4 by decide, if_true, if_false]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_mul, hY1', bv_toNat_ofNat_lt (un21 / d1) (by omega), bv_toNat_ofNat_lt (un21 % d1) (by omega),
          bv_toNat_ofNat_lt un21 (by omega)]
        have hm := Nat.mul_comm d1 (un21 / d1)
        have hp : un21 / d1 * d1 ≤ un21 := by omega
        rw [Nat.mod_eq_of_lt (show d1 * (un21 / d1) < 2 ^ 64 by have := Y.isLt; omega)]
        have : un21 < 2 ^ 64 := by have := Y.isLt; omega
        omega
      · simp [setReg, r2, hYo]
      · simp only [setReg]; simp [r8]
        apply BitVec.eq_of_toNat_eq
        rw [hY0', bv_toNat_ofNat_lt _ (by omega)]
      · simp only [setReg]; simp
        apply BitVec.eq_of_toNat_eq
        rw [hun0, bv_toNat_ofNat_lt _ (by omega)]
      · simp [setReg, h10]
    · simp only [setReg]; simp [hY1']
    · simp only [setReg]
      simp only [hY1', show (9 : Nat) ≠ 29 by decide, show (9 : Nat) ≠ 16 by decide, if_true, if_false, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_mul, hU4, hY1', bv_toNat_ofNat_lt (A / d1) (by omega), bv_toNat_ofNat_lt (A % d1) (by omega)]
      have hm := Nat.mul_comm d1 (A / d1)
      have hAl : A < 2 ^ 64 := by have := Y.isLt; omega
      have hp : A / d1 * d1 ≤ A := by omega
      rw [Nat.mod_eq_of_lt (show d1 * (A / d1) < 2 ^ 64 by omega)]
      omega
    · simp [setReg, hYo]
    · simp only [setReg]; simp
      apply BitVec.eq_of_toNat_eq
      rw [hY0', bv_toNat_ofNat_lt _ (by omega)]
    · simp [setReg]

end Fv256.Arm64.Div64
