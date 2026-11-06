import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.ExpMath
import Fv256.ExpFinal
import Fv256.ExpPro
import Fv256.UtilF

/-! Arithmetic facts about the entry of arm64 `Exp`: bit length of the exponent, the even-base early exit. -/

open Fv256.Spec

namespace Fv256.Arm64.ExpEntry

theorem nreg (c K : Nat) (hc : c ≤ 64) (hK : K < 2 ^ 62) :
    64#64 - BitVec.ofNat 64 c + BitVec.ofNat 64 K = BitVec.ofNat 64 (64 - c + K) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem nreg0 (c : Nat) (hc : c ≤ 64) : 64#64 - BitVec.ofNat 64 c = BitVec.ofNat 64 (64 - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem nmem (c K : Nat) (hc : c ≤ 64) (hK : K < 2 ^ 62) :
    (18446744073709551616 - c % 18446744073709551616 + 64 + K) % 18446744073709551616 = 64 - c + K := by
  omega

theorem toInt_n (n : Nat) (h : n < 2 ^ 62) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_ofNat]; omega)]
  simp [BitVec.toNat_ofNat]
  omega

theorem clz_le (e : Nat) (h : e < 2 ^ 64) : Janus.Arm64.clzNat 64 e ≤ 64 := by
  have := Fv256.Util.clz_bl 64 e h
  omega

/-- bit length of the exponent when the top nonzero limb is limb 0 (possibly all zero) -/
theorem bl0 (e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (z1 : e1 = 0) (z2 : e2 = 0) (z3 : e3 = 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) = 64 - Janus.Arm64.clzNat 64 e0 := by
  subst z1 z2 z3
  have := Fv256.Util.clz_bl 64 e0 h0
  simp only [Nat.mul_zero, Nat.add_zero]
  omega

theorem bl1 (e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (nz : e1 ≠ 0) (z2 : e2 = 0) (z3 : e3 = 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) = 64 - Janus.Arm64.clzNat 64 e1 + 64 := by
  subst z2 z3
  simp only [Nat.mul_zero, Nat.add_zero]
  have := Fv256.F.n_top1 e0 e1 h0 h1 nz
  have hc := (Fv256.B.clz_norm e1 nz h1).1
  omega

theorem bl2 (e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (nz : e2 ≠ 0) (z3 : e3 = 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) = 64 - Janus.Arm64.clzNat 64 e2 + 128 := by
  subst z3
  simp only [Nat.mul_zero, Nat.add_zero]
  have := Fv256.F.n_top2 e0 e1 e2 h0 h1 h2 nz
  have hc := (Fv256.B.clz_norm e2 nz h2).1
  omega

theorem bl3 (e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (h3 : e3 < 2 ^ 64) (nz : e3 ≠ 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) = 64 - Janus.Arm64.clzNat 64 e3 + 192 := by
  have := Fv256.F.n_top3 e0 e1 e2 e3 h0 h1 h2 h3 nz
  have hc := (Fv256.B.clz_norm e3 nz h3).1
  omega

/-- an even base with a large exponent gives `0` -/
theorem early (B E : Nat) (hB : B % 2 = 0) (hn : 8 < bitLen E) : 0 = Fv256.F.expSpec B E := by
  have := Fv256.F.ge256_of_bitLen E hn
  unfold Fv256.F.expSpec
  exact (Fv256.F.even_exp_zero _ _ hB this).symm

theorem even_split (b0 b1 b2 b3 : Nat) (h : b0 % 2 = 0) : (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) % 2 = 0 := by
  omega

theorem expIter_lt (k r b e : Nat) (hr : r < 2 ^ 256) (hb : b < 2 ^ 256) :
    (Fv256.F.expIter k (r, b, e)).1 < 2 ^ 256 ∧ (Fv256.F.expIter k (r, b, e)).2.1 < 2 ^ 256 := by
  rw [Fv256.F.expIter_eq k r b e hr hb]
  exact ⟨Nat.mod_lt _ (Nat.two_pow_pos _), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem hev_odd (b0 n : Nat) (h : ((BitVec.ofNat 64 b0).getLsbD 0 == true) = true) : b0 % 2 = 0 → n ≤ 8 := by
  intro h0
  rw [Fv256.F.lsb_w64] at h
  simp at h
  omega

theorem hev_small0 (b0 c : Nat) (hc : c ≤ 64) (h : (64#64 - BitVec.ofNat 64 c).toInt ≤ 8) : b0 % 2 = 0 → 64 - c ≤ 8 := by
  intro _
  rw [nreg0 c hc, toInt_n _ (by omega)] at h
  omega

theorem hev_smallK (b0 c K : Nat) (hc : c ≤ 64) (hK : K ≤ 192) (h : (64#64 - BitVec.ofNat 64 c + BitVec.ofNat 64 K).toInt ≤ 8) :
    b0 % 2 = 0 → 64 - c + K ≤ 8 := by
  intro _
  rw [nreg c K hc (by omega), toInt_n _ (by omega)] at h
  omega

theorem even_lsb (b0 : Nat) (h : ¬((BitVec.ofNat 64 b0).getLsbD 0 == true) = true) : b0 % 2 = 0 := by
  rw [Fv256.F.lsb_w64] at h
  simpa using h

theorem big0 (b0 c : Nat) (hc : c ≤ 64) (h : ¬(64#64 - BitVec.ofNat 64 c).toInt ≤ 8) : 8 < 64 - c := by
  rw [nreg0 c hc, toInt_n _ (by omega)] at h
  omega

theorem bigK (c K : Nat) (hc : c ≤ 64) (hK : K ≤ 192) (h : ¬(64#64 - BitVec.ofNat 64 c + BitVec.ofNat 64 K).toInt ≤ 8) : 8 < 64 - c + K := by
  rw [nreg c K hc (by omega), toInt_n _ (by omega)] at h
  omega

theorem early_t0 (b e0 : Nat) (h0 : e0 < 2 ^ 64) (hb : b % 2 = 0) (hbig : 8 < 64 - Janus.Arm64.clzNat 64 e0) :
    0 = Fv256.F.expSpec b e0 := by
  apply early b e0 hb
  have := Fv256.Util.clz_bl 64 e0 h0
  omega

theorem early_t1 (b e0 e1 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (nz : e1 ≠ 0) (hb : b % 2 = 0)
    (hbig : 8 < 64 - Janus.Arm64.clzNat 64 e1 + 64) : 0 = Fv256.F.expSpec b (e0 + 2 ^ 64 * e1) := by
  apply early b _ hb
  have := Fv256.F.n_top1 e0 e1 h0 h1 nz
  have hc := (Fv256.B.clz_norm e1 nz h1).1
  omega

theorem early_t2 (b e0 e1 e2 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (nz : e2 ≠ 0) (hb : b % 2 = 0)
    (hbig : 8 < 64 - Janus.Arm64.clzNat 64 e2 + 128) : 0 = Fv256.F.expSpec b (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2) := by
  apply early b _ hb
  have := Fv256.F.n_top2 e0 e1 e2 h0 h1 h2 nz
  have hc := (Fv256.B.clz_norm e2 nz h2).1
  omega

theorem early_t3 (b e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (h3 : e3 < 2 ^ 64) (nz : e3 ≠ 0)
    (hb : b % 2 = 0) (hbig : 8 < 64 - Janus.Arm64.clzNat 64 e3 + 192) :
    0 = Fv256.F.expSpec b (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) := by
  apply early b _ hb
  have := Fv256.F.n_top3 e0 e1 e2 e3 h0 h1 h2 h3 nz
  have hc := (Fv256.B.clz_norm e3 nz h3).1
  omega

theorem nm0a (c : Nat) (hc : c ≤ 64) : (18446744073709551616 - c + 64) % 18446744073709551616 = 64 - c := by omega

theorem nm0b (c : Nat) (hc : c ≤ 64) : (18446744073709551616 - c % 18446744073709551616 + 64) % 18446744073709551616 = 64 - c := by omega

theorem nm0c (c : Nat) (hc : c ≤ 64) : (18446744073709551616 - c - 18446744073709551552) % 18446744073709551616 = 64 - c := by omega

theorem nmK (c K : Nat) (hc : c ≤ 64) (hK : K ≤ 192) :
    ((18446744073709551616 - c + 64) % 18446744073709551616 + K) % 18446744073709551616 = 64 - c + K := by omega

end Fv256.Arm64.ExpEntry
