import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

/-!
# `(*uint256.Int).Float64() float64` (arm64)

**Guarantee.** For every receiver `x` (`X0`) whose 32 bytes are readable (below `2^48`) and every Go call state such that the
stack-growth check falls through (`GuardOK s 0`), the 88 bytes below `SP` (the 80-byte frame, the saved frame pointer and the
callee-local copy of the shifted number) are writable and aligned (`StackOK s 88 0`), they do not overlap `x`, and `FPCR = 0`:
the call returns (no fault, no panic), obeys the ABI, `D0` (read as 64 bits) is `Fv256.B.float64BitsTrunc` of the number at `x`
(IEEE 754 binary64 bits: round-to-nearest-even `convertFromInt` below `2^64`, truncation of the 52 bits after the leading one
from `2^64` on, as the library does), and no byte outside the 88-byte window changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns with the stated result.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option maxHeartbeats 8000000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0)
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsTrunc (val256 s.mem x.toNat) ∧
        OnlyWrites s.mem s'.mem (s.sp.toNat - 88) 88) := by
  intro ret hret s hs ⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  have c3 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
  have hor : (s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 8) 8 ||| s.mem.readLE (x.toNat + 24) 8 = 0) ↔
      (s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0) := by
    simp [Nat.or_eq_zero_iff, and_assoc]
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE (x.toNat + 16) 8 = 0
    · by_cases h1 : s.mem.readLE (x.toNat + 8) 8 = 0
      · have hor3 : (s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 8) 8 = 0) ↔
            (s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0) := by
          simp [Nat.or_eq_zero_iff]
        janus_run [hf, hor, hor3, h3, h2, h1]
        have hlt : Janus.Float.fromInt Janus.Float.binary64 .rne (s.mem.readLE x.toNat 8) < 2 ^ 64 :=
          Janus.Float.fromInt_lt Janus.Float.binary64 .rne _
        have hx0 := Util.readLE8_lt s.mem x.toNat
        simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat]
        rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl]
        simp only [Bool.true_or, ite_true]
        unfold Fv256.B.float64BitsTrunc
        rw [if_pos (by simpa using hx0)]
        simp only [Nat.reducePow] at hlt hx0 ⊢
        omega
      · have c1 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
        obtain ⟨k1, hk1⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = k := ⟨_, rfl⟩
        have hk1' : k1 < 64 := by
          rcases c1 with h | h
          · exact absurd h h1
          · rw [hk1] at h; exact h
        janus_run [hf, hor, h3, h2, h1, hk1] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
        generalize hN : (257#64 - (64#64 - BitVec.ofNat 64 k1 + 64#64)) = N at *
        have hNk : N.toNat = 129 + k1 := by
          have := congrArg BitVec.toNat hN
          simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
          omega
        janus_run [hNk]
        all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, Fv256.B.extract12_append])
        · have hk63 : k1 = 63 := by omega
          subst hk63
          simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, Nat.reduceMul, Nat.reducePow, Nat.reduceLT, ite_true, Nat.pow_zero, Nat.mul_one]
          rw [h3, h2]
          have hx0 := Util.readLE8_lt s.mem x.toNat
          have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
          have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
          have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 := by
            have : 1 ≤ s.mem.readLE (x.toNat + 8) 8 := Nat.pos_of_ne_zero h1
            omega
          have hbl := Fv256.B.f64_bl1 _ _ 63 hx0 hx1 h1 hk1
          have hF := Fv256.B.lsh_top3 _ _ 0 0 0 (by omega) hx0 hx1 (by decide) (by decide)
          simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx0] at hF
          refine Eq.trans ?_ (Fv256.B.f64_gen _ 192 (s.mem.readLE x.toNat 8) (by omega) (by omega) (by omega) hVlt hVge (by simpa using hF.symm))
          have hc : (BitVec.ofNat 64 (18446744073709551616 - 63 - 18446744073709551552 + 64) + 1022#64).toNat = 1087 := by decide
          simp only [hc, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt hx0]
          omega
        · rw [h3, h2]
          have hx0 := Util.readLE8_lt s.mem x.toNat
          have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
          have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
          have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 := by
            have : 1 ≤ s.mem.readLE (x.toNat + 8) 8 := Nat.pos_of_ne_zero h1
            omega
          have hbl := Fv256.B.f64_bl1 _ _ k1 hx0 hx1 h1 hk1
          have hF := Fv256.B.lsh_top2 _ _ 0 0 (1 + k1) (by omega) hx0 hx1 (by decide) (by decide)
          refine Eq.trans ?_ (Fv256.B.f64_gen _ (128 + (1 + k1)) (s.mem.readLE (x.toNat + 8) 8 * 2 ^ (1 + k1) % 18446744073709551616 + s.mem.readLE x.toNat 8 / 2 ^ (64 - (1 + k1))) (by omega) (by omega) (by omega) hVlt hVge hF.symm)
          have hE : (BitVec.ofNat 64 ((18446744073709551616 - k1 + 64) % 18446744073709551616 + 64) + 1022#64).toNat = 1279 - (128 + (1 + k1)) := by
            simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
          have hq1 : (129 + k1 - 128) % 64 = 1 + k1 := by omega
          have hc : 18446744073709551616 - (129 + k1) - 18446744073709551424 = 64 - (1 + k1) := by omega
          have hFe := Util.shl_or_bv (s.mem.readLE (x.toNat + 8) 8) (s.mem.readLE x.toNat 8) (1 + k1) (by omega) hx1 hx0
          rw [hE, hq1, hc, hFe]
          have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 8) 8) (s.mem.readLE x.toNat 8) (1 + k1) (by omega) hx0
          rw [Nat.mod_eq_of_lt hlt]
          omega
    · have c2 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
      obtain ⟨k2, hk2⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = k := ⟨_, rfl⟩
      have hk2' : k2 < 64 := by
        rcases c2 with h | h
        · exact absurd h h2
        · rw [hk2] at h; exact h
      have hor2 : (s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 8) 8 = 0) ↔
          (s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0) := by
        simp [Nat.or_eq_zero_iff]
      janus_run [hf, hor, hor2, h3, h2, hk2] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
      generalize hN : (257#64 - (64#64 - BitVec.ofNat 64 k2 + 128#64)) = N at *
      have hNk : N.toNat = 65 + k2 := by
        have := congrArg BitVec.toNat hN
        simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        omega
      janus_run [hNk]
      all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, Fv256.B.extract12_append])
      · have hk63 : k2 = 63 := by omega
        subst hk63
        simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, Nat.reduceMul, Nat.reducePow, Nat.reduceLT, ite_false, Nat.pow_zero, Nat.mul_one]
        rw [h3]
        have hx0 := Util.readLE8_lt s.mem x.toNat
        have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
        have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
        have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
        have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 := by
          have : 1 ≤ s.mem.readLE (x.toNat + 16) 8 := Nat.pos_of_ne_zero h2
          omega
        have hbl := Fv256.B.f64_bl2 _ _ _ 63 hx0 hx1 hx2 h2 hk2
        have hF := Fv256.B.lsh_top2 _ _ _ 0 0 (by omega) hx0 hx1 hx2 (by decide)
        have hx0' : s.mem.readLE x.toNat 8 / 2 ^ (64 - 0) = 0 := Nat.div_eq_of_lt (by simpa using hx0)
        simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, hx0', Nat.mod_eq_of_lt hx1] at hF
        refine Eq.trans ?_ (Fv256.B.f64_gen _ 128 (s.mem.readLE (x.toNat + 8) 8) (by omega) (by omega) (by omega) hVlt hVge (by simpa using hF.symm))
        have h0t : (0#64).toNat = 0 := rfl
        have hc : (129#64 + 1022#64).toNat = 1151 := by decide
        simp only [h0t, hc, Nat.or_zero]
        omega
      · rw [h3]
        have hx0 := Util.readLE8_lt s.mem x.toNat
        have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
        have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
        have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
        have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 := by
          have : 1 ≤ s.mem.readLE (x.toNat + 16) 8 := Nat.pos_of_ne_zero h2
          omega
        have hbl := Fv256.B.f64_bl2 _ _ _ k2 hx0 hx1 hx2 h2 hk2
        have hF := Fv256.B.lsh_top1 _ _ _ 0 (1 + k2) (by omega) hx0 hx1 hx2 (by decide)
        refine Eq.trans ?_ (Fv256.B.f64_gen _ (64 + (1 + k2)) (s.mem.readLE (x.toNat + 16) 8 * 2 ^ (1 + k2) % 18446744073709551616 + s.mem.readLE (x.toNat + 8) 8 / 2 ^ (64 - (1 + k2))) (by omega) (by omega) (by omega) hVlt hVge hF.symm)
        have hE : (BitVec.ofNat 64 ((18446744073709551616 - k2 + 64) % 18446744073709551616 + 128) + 1022#64).toNat = 1279 - (64 + (1 + k2)) := by
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hq1 : (65 + k2 - 64) % 64 = 1 + k2 := by omega
        have hc : 18446744073709551616 - (65 + k2) - 18446744073709551488 = 64 - (1 + k2) := by omega
        have hFe := Util.shl_or_bv (s.mem.readLE (x.toNat + 16) 8) (s.mem.readLE (x.toNat + 8) 8) (1 + k2) (by omega) hx2 hx1
        rw [hE, hq1, hc]
        rw [hFe]
        have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 16) 8) (s.mem.readLE (x.toNat + 8) 8) (1 + k2) (by omega) hx1
        rw [Nat.mod_eq_of_lt hlt]
        omega
  · obtain ⟨k3, hk3⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = k := ⟨_, rfl⟩
    have hk3' : k3 < 64 := by
      rcases c3 with h | h
      · exact absurd h h3
      · rw [hk3] at h; exact h
    janus_run [hf, hor, h3, hk3] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
    generalize hN : (257#64 - (64#64 - BitVec.ofNat 64 k3 + 192#64)) = N at *
    have hNk : N.toNat = 1 + k3 := by
      have := congrArg BitVec.toNat hN
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    janus_run [hNk]
    all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat, Fv256.B.extract12_append])
    · have hx0 := Util.readLE8_lt s.mem x.toNat
      have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
      have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
      have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
      have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
          340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 < 2 ^ 256 := by
        omega
      have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
          340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 := by
        have : 1 ≤ s.mem.readLE (x.toNat + 24) 8 := Nat.pos_of_ne_zero h3
        omega
      have hbl := Fv256.B.f64_bl3 _ _ _ _ k3 hx0 hx1 hx2 hx3 h3 hk3
      have hF := Fv256.B.lsh_top0 _ _ _ _ (1 + k3) (by omega) hx0 hx1 hx2 hx3
      refine Eq.trans ?_ (Fv256.B.f64_gen _ (1 + k3) _ (by omega) (by omega) (by omega) hVlt hVge hF.symm)
      have hE : (BitVec.ofNat 64 ((18446744073709551616 - k3 + 64) % 18446744073709551616 + 192) + 1022#64).toNat = 1279 - (1 + k3) := by
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hamt : (18446744073709551616 - (1 + k3) - 18446744073709551552) % 64 = (64 - (1 + k3)) % 64 := by omega
      have hFe := Util.shl_or_bv0 (s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE (x.toNat + 16) 8) (1 + k3) (by omega) (by omega) hx3 hx2
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hamt, Nat.mod_eq_of_lt hx2, Nat.reducePow, Nat.mod_eq_of_lt (show (1 + k3) < 18446744073709551616 by omega)]
      rw [hE, Nat.mod_eq_of_lt (show 1 + k3 < 64 by omega), hFe]
      have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE (x.toNat + 16) 8) (1 + k3) (by omega) hx2
      rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hk63 : k3 = 63 := by omega
      subst hk63
      simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, Nat.reduceMul, Nat.reducePow, Nat.reduceLT, ite_false, Nat.pow_zero, Nat.mul_one]
      have hx0 := Util.readLE8_lt s.mem x.toNat
      have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
      have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
      have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
      have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
          340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 < 2 ^ 256 := by
        omega
      have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
          340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
          6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 := by
        have : 1 ≤ s.mem.readLE (x.toNat + 24) 8 := Nat.pos_of_ne_zero h3
        omega
      have hbl := Fv256.B.f64_bl3 _ _ _ _ 63 hx0 hx1 hx2 hx3 h3 hk3
      have hF := Fv256.B.lsh_top1 _ _ _ _ 0 (by omega) hx0 hx1 hx2 hx3
      have hx1' : s.mem.readLE (x.toNat + 8) 8 / 2 ^ (64 - 0) = 0 := Nat.div_eq_of_lt (by simpa using hx1)
      simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, hx1', Nat.mod_eq_of_lt hx2] at hF
      refine Eq.trans ?_ (Fv256.B.f64_gen _ 64 (s.mem.readLE (x.toNat + 16) 8) (by omega) (by omega) (by omega) hVlt hVge (by simpa using hF.symm))
      have h0t : (0#64).toNat = 0 := rfl
      have hc : (193#64 + 1022#64).toNat = 1215 := by decide
      simp only [h0t, hc, Nat.or_zero]
      omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem x false ∧ GuardOK s0 0 ∧ StackOK s0 88 0 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 88) 88 ∧ s0.fpcr = 0 :=
  ⟨⟨by decide, by decide⟩, by unfold GuardOK; decide, by unfold StackOK; decide, by unfold Disjoint; decide, rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0) :=
  ⟨ret, s0, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.getV 0 64 = Fv256.B.float64BitsTrunc (val256 s0.mem x.toNat) ∧
      OnlyWrites s0.mem s'.mem (s0.sp.toNat - 88) 88 :=
  correctness x ret hret s0 setup hpre

end Witness

end Fv256.Arm64.Float64
