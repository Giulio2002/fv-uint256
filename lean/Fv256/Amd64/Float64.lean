import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

/-!
# `(*uint256.Int).Float64() float64` (amd64)

**Guarantee.** For every receiver `x` (`RAX`) whose 32 bytes are readable (below `2^48`) and every Go call in which the stack-growth
check falls through (`StackGuardOK s 0`), the window `[RSP-80, RSP+8)` (the 0x50-byte frame with the saved frame pointer and the
pushed return address of the callee, plus the caller's return-address slot) is writable, `x` does not overlap it, and the SSE control
word has the Go ABI's control bits (`GoMXCSR`): the call returns (no fault, no panic), obeys the ABI, the low 64 bits of `XMM0` are
`Fv256.B.float64Bits` of the number at `x` (IEEE 754 binary64 bits: round-to-nearest-even `convertFromInt` below `2^64`, truncation
of the 52 bits after the leading one from `2^64` on, as the library does), and no byte outside the window changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns with the stated result.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

namespace Fv256.Amd64.Float64

set_option maxHeartbeats 8000000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s)
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64Bits (valueAt s x 32) ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat - 80) 88 ((s.regs regSP).toNat - 80) 88) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hxw, hx⟩, hds, hm⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  have hor : (s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 8) 8 ||| s.mem.readLE (x.toNat + 24) 8 = 0) ↔
      (s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0) := by
    simp [Nat.or_eq_zero_iff, and_assoc]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE (x.toNat + 16) 8 = 0
    · by_cases h1 : s.mem.readLE (x.toNat + 8) 8 = 0
      · janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hor, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, h3, h2, h1]
        all_goals (refine ⟨?_, ?_⟩)
        all_goals (first | (simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]; done) | skip)
        · have hX0 := Util.readLE8_lt s.mem x.toNat
          generalize hX : s.mem.readLE x.toNat 8 = X at *
          have hxt : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hX0
          generalize hxv : BitVec.ofNat 64 X = xv at *
          subst hxt
          have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
          have hfl := fromInt_lt binary64 .rne
          unfold Fv256.B.float64Bits
          rw [if_pos xv.isLt]
          have hmsb : xv.msb = true := by assumption
          have hx : 2 ^ 63 ≤ xv.toNat := by
            rw [BitVec.msb_eq_decide] at hmsb; simp at hmsb; omega
          have hy : (xv >>> 1 ||| BitVec.setWidth 64 (BitVec.setWidth 32 xv &&& 1#32)).toNat =
              xv.toNat / 2 ||| xv.toNat % 2 := by
            rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_and,
              BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow, show (1#32).toNat = 1 from rfl,
              Nat.and_one_is_mod, Nat.pow_one]
            first | (with_reducible congr 1; omega) | (congr 1; omega)
          have hylt : xv.toNat / 2 ||| xv.toNat % 2 < 2 ^ (64 - 1) := by
            have := or_bit (xv.toNat / 2) (xv.toNat % 2) (Nat.mod_lt _ (by decide))
            have hb : xv.toNat / 2 % 2 ||| xv.toNat % 2 < 2 :=
              Nat.or_lt_two_pow (n := 1) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
            omega
          rw [hy, ofInt_ieee hc]
          simp only [hylt, ite_true]
          have h1 : fromInt binary64 .rne ((xv.toNat / 2 ||| xv.toNat % 2 : Nat) : Int) < 18446744073709551616 :=
            hfl _
          rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega : fromInt binary64 .rne
            ((xv.toNat / 2 ||| xv.toNat % 2 : Nat) : Int) < 340282366920938463463374607431768211456)]
          rw [u64_big hc xv.toNat hx xv.isLt]
          have h2 : fromInt binary64 .rne (xv.toNat : Int) < 18446744073709551616 := hfl _
          dsimp only
          omega
        · have hX0 := Util.readLE8_lt s.mem x.toNat
          generalize hX : s.mem.readLE x.toNat 8 = X at *
          have hxt : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hX0
          have hc : IEEEMode (⟨.rne, false, false⟩ : Ctl) := ⟨rfl, rfl⟩
          have hfl := fromInt_lt binary64 .rne
          unfold Fv256.B.float64Bits
          rw [if_pos (by simpa using hX0)]
          rw [ofInt_ieee hc]
          have hmsb : ¬ (BitVec.ofNat 64 X).msb = true := by assumption
          have hx : X < 2 ^ 63 := by
            rw [BitVec.msb_eq_decide] at hmsb; simp only [hxt] at hmsb; simp at hmsb; omega
          have hlt : fromInt binary64 .rne (X : Int) < 18446744073709551616 := hfl _
          simp only [show X < 2 ^ (64 - 1) from hx, ite_true]
          rw [Nat.mod_eq_of_lt hlt]
          exact Nat.mod_eq_of_lt (by omega)
      · have c1 := Fv256.B.clz_cases _ hx1
        obtain ⟨k1, hk1⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = k := ⟨_, rfl⟩
        have hk1' : k1 < 64 := by
          rcases c1 with h | h
          · exact absurd h h1
          · rw [hk1] at h; exact h
        janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hor, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, h3, h2, h1, hk1] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
        generalize hN : (0#64 - (BitVec.ofNat 64 (63 - k1) - 192#64)) = N at *
        have hNk : N.toNat = 129 + k1 := by
          have := congrArg BitVec.toNat hN
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
          omega
        janus64_run [Util.readLE_32, hNk]
        all_goals (refine ⟨?_, ?_⟩)
        all_goals (first | (simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]; done) | skip)
        · have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
          have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
              340282366920938463463374607431768211456 * 0 +
              6277101735386680763835789423207666416102355444464034512896 * 0 := by
            have : 1 ≤ s.mem.readLE (x.toNat + 8) 8 := Nat.pos_of_ne_zero h1
            omega
          have hbl := Fv256.B.f64_bl1 _ _ k1 hx0 hx1 h1 hk1
          have hF := Fv256.B.lsh_top2 _ _ 0 0 (1 + k1) (by omega) hx0 hx1 (by decide) (by decide)
          have hg := Fv256.B.f64_gen _ (128 + (1 + k1)) (s.mem.readLE (x.toNat + 8) 8 * 2 ^ (1 + k1) % 18446744073709551616 + s.mem.readLE x.toNat 8 / 2 ^ (64 - (1 + k1))) (by omega) (by omega) (by omega) hVlt hVge hF.symm
          simp only [Nat.mul_zero, Nat.add_zero] at hVlt hVge hbl hg
          have hmk : (if 18446744073709551616 - (18446744073709551424 + (129 + k1)) < 64 then 18446744073709551615#64 else 0#64) = 18446744073709551615#64 := if_pos (by omega)
          rw [hmk, Fv256.B.mask_and]
          have e1 : (18446744073709551616 - (129 + k1)) % 64 = 64 - (1 + k1) := by omega
          have e2 : (129 + k1) % 64 = 1 + k1 := by omega
          rw [e1, e2, Fv256.B.assemble_bv _ (63 - k1 + 65) (by omega), Fv256.B.shld_toNat _ _ (1 + k1) (by omega) (by omega) hx0 hx1]
          have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 8) 8) (s.mem.readLE x.toNat 8) (1 + k1) (by omega) hx0
          rw [Fv256.B.f64_asm_eq _ (1279 - (128 + (1 + k1))) (by simp only [Nat.reducePow] at hlt ⊢; omega) (by omega)] at hg
          simp only [Nat.reducePow] at hlt hg ⊢
          omega
        · have hk63 : k1 = 63 := by omega
          subst hk63
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
          simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hx0, Nat.mul_zero] at hF
          have hg := Fv256.B.f64_gen _ 192 (s.mem.readLE x.toNat 8) (by omega) (by omega) (by omega) hVlt hVge (by simpa using hF.symm)
          simp only [Nat.mul_zero, Nat.add_zero] at hVlt hVge hbl hg
          have hmk : (if 129 + 63 - 192 < 64 then 18446744073709551615#64 else 0#64).toNat = 18446744073709551615 := by decide
          have hand : s.mem.readLE x.toNat 8 &&& 18446744073709551615 = s.mem.readLE x.toNat 8 := by
            rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx0]
          rw [hmk, hand, Nat.mod_eq_of_lt hx0, Fv256.B.assemble_toNat (s.mem.readLE x.toNat 8) (63 - 63 + 65) hx0 (by omega)]
          rw [Fv256.B.f64_asm_eq _ (1279 - 192) hx0 (by omega)] at hg
          omega
    · have c2 := Fv256.B.clz_cases _ hx2
      obtain ⟨k2, hk2⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = k := ⟨_, rfl⟩
      have hk2' : k2 < 64 := by
        rcases c2 with h | h
        · exact absurd h h2
        · rw [hk2] at h; exact h
      janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hor, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, h3, h2, hk2] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
      generalize hN : (0#64 - (BitVec.ofNat 64 (63 - k2) - 128#64)) = N at *
      have hNk : N.toNat = 65 + k2 := by
        have := congrArg BitVec.toNat hN
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
        omega
      janus64_run [Util.readLE_32, hNk]
      all_goals (refine ⟨?_, ?_⟩)
      all_goals (first | (simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]; done) | skip)
      · have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 < 2 ^ 256 := by omega
        have hVge : 2 ^ 64 ≤ s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
            340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 +
            6277101735386680763835789423207666416102355444464034512896 * 0 := by
          have : 1 ≤ s.mem.readLE (x.toNat + 16) 8 := Nat.pos_of_ne_zero h2
          omega
        have hbl := Fv256.B.f64_bl2 _ _ _ k2 hx0 hx1 hx2 h2 hk2
        have hF := Fv256.B.lsh_top1 _ _ _ 0 (1 + k2) (by omega) hx0 hx1 hx2 (by decide)
        have hg := Fv256.B.f64_gen _ (64 + (1 + k2)) (s.mem.readLE (x.toNat + 16) 8 * 2 ^ (1 + k2) % 18446744073709551616 + s.mem.readLE (x.toNat + 8) 8 / 2 ^ (64 - (1 + k2))) (by omega) (by omega) (by omega) hVlt hVge hF.symm
        simp only [Nat.mul_zero, Nat.add_zero] at hVlt hVge hbl hg
        have hmk : (if 18446744073709551616 - (18446744073709551488 + (65 + k2)) < 64 then 18446744073709551615#64 else 0#64) = 18446744073709551615#64 := if_pos (by omega)
        rw [hmk, Fv256.B.and_mask]
        have e1 : (18446744073709551616 - (65 + k2)) % 64 = 64 - (1 + k2) := by omega
        have e2 : (65 + k2) % 64 = 1 + k2 := by omega
        rw [e1, e2, Fv256.B.assemble_bv _ (63 - k2 + 129) (by omega), Fv256.B.shld_toNat _ _ (1 + k2) (by omega) (by omega) hx1 hx2]
        have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 16) 8) (s.mem.readLE (x.toNat + 8) 8) (1 + k2) (by omega) hx1
        rw [Fv256.B.f64_asm_eq _ (1279 - (64 + (1 + k2))) (by simp only [Nat.reducePow] at hlt ⊢; omega) (by omega)] at hg
        simp only [Nat.reducePow] at hlt hg ⊢
        omega
      · have hk63 : k2 = 63 := by omega
        subst hk63
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
        simp only [Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, hx0', Nat.mod_eq_of_lt hx1, Nat.mul_zero] at hF
        have hg := Fv256.B.f64_gen _ 128 (s.mem.readLE (x.toNat + 8) 8) (by omega) (by omega) (by omega) hVlt hVge hF.symm
        simp only [Nat.mul_zero, Nat.add_zero] at hVlt hVge hbl hg
        have hm : (18446744073709551616 - (18446744073709551424 + (65 + 63)) < 64) = False := by decide
        simp only [hm, if_false, Nat.reduceSub, Nat.reduceAdd]
        have h0 : (0#64 &&& BitVec.ofNat 64 (s.mem.readLE x.toNat 8)) = 0#64 := by simp
        rw [h0, BitVec.zero_or, Fv256.B.assemble_toNat _ (63 - 63 + 129) hx1 (by omega)]
        rw [Fv256.B.f64_asm_eq _ (1279 - 128) hx1 (by omega)] at hg
        omega
  · have c3 := Fv256.B.clz_cases _ hx3
    obtain ⟨k3, hk3⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = k := ⟨_, rfl⟩
    have hk3' : k3 < 64 := by
      rcases c3 with h | h
      · exact absurd h h3
      · rw [hk3] at h; exact h
    janus64_run [Util.readLE_32, GoMXCSR.ctl hm, GoMXCSR.unmasked hm, GoMXCSR.mod hm, hor, Fv256.B.or3_zero_iff, Fv256.B.or2_zero_iff, h3, hk3] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
    generalize hN : (0#64 - (BitVec.ofNat 64 (63 - k3) - 64#64)) = N at *
    have hNk : N.toNat = 1 + k3 := by
      have := congrArg BitVec.toNat hN
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega
    janus64_run [Util.readLE_32, hNk]
    all_goals (refine ⟨?_, ?_⟩)
    all_goals (first | (simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]; done) | skip)
    · have hVlt : s.mem.readLE x.toNat 8 + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 +
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
      have hFun := Fv256.B.funnel (s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE (x.toNat + 16) 8) (1 + k3) (by omega) hx3 hx2
      rw [Nat.mod_eq_of_lt (show 1 + k3 < 64 by omega)]
      simp only [Nat.reducePow] at hFun
      rw [hFun]
      have hlt := Util.lo_hi_lt (s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE (x.toNat + 16) 8) (1 + k3) (by omega) hx2
      have hg := Fv256.B.f64_gen _ (1 + k3) _ (by omega) (by omega) (by omega) hVlt hVge hF.symm
      rw [Fv256.B.assemble_toNat _ (63 - k3 + 193) (by omega) (by omega)]
      rw [Fv256.B.f64_asm_eq _ (1279 - (1 + k3)) (by omega) (by omega)] at hg
      have hm : (1279 - (1 + k3)) = 63 - k3 + 193 + 1022 - 0 := by omega
      omega
    · have hk63 : k3 = 63 := by omega
      subst hk63
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
      have hg := Fv256.B.f64_gen _ 64 (s.mem.readLE (x.toNat + 16) 8) (by omega) (by omega) (by omega) hVlt hVge (by simpa using hF.symm)
      have hm : (18446744073709551616 - (18446744073709551488 + (1 + 63)) < 64) = False := by decide
      simp only [hm, if_false, Nat.reduceSub, Nat.reduceAdd]
      have h0 : (BitVec.ofNat 64 (s.mem.readLE (x.toNat + 8) 8) &&& 0#64) = 0#64 := by simp
      rw [h0, BitVec.zero_or]
      rw [Fv256.B.assemble_toNat _ (63 - 63 + 193) hx2 (by omega)]
      rw [Fv256.B.f64_asm_eq _ (1279 - 64) hx2 (by omega)] at hg
      omega


namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 80 8 ∧ Buffer s0 x 32 false ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 80 ∨ (s0.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold regSP; decide,
    by unfold GoMXCSR; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s) :=
  ⟨ret, s0, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64Bits (valueAt s0 x 32) ∧
      Util.OnlyWrites2 s0.mem s'.mem ((s0.regs regSP).toNat - 80) 88 ((s0.regs regSP).toNat - 80) 88 :=
  correctness x ret hret s0 setup hpre

end Witness

end Fv256.Amd64.Float64
