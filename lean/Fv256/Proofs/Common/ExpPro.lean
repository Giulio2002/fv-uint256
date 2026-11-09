import Fv256.Proofs.Common.UdivMathB
import Fv256.Proofs.Common.ExpFinal
import Fv256.Proofs.Common.UtilF
namespace Fv256.F
open Fv256.Spec

theorem bitLen_shift (lo k w : Nat) (hlo : lo < 2 ^ k) (hw : w ≠ 0) : bitLen (lo + 2 ^ k * w) = bitLen w + k := by
  have hw0 : 0 < w := Nat.pos_of_ne_zero hw
  have hp : 0 < 2 ^ k := Nat.two_pow_pos _
  have hne : lo + 2 ^ k * w ≠ 0 := by
    have : 2 ^ k * 1 ≤ 2 ^ k * w := Nat.mul_le_mul_left _ hw0
    omega
  unfold bitLen
  rw [if_neg hne, if_neg hw]
  have h1 : 2 ^ Nat.log2 w ≤ w := Nat.log2_self_le hw
  have h2 : w < 2 ^ (Nat.log2 w + 1) := Nat.lt_log2_self
  have : Nat.log2 (lo + 2 ^ k * w) = Nat.log2 w + k := by
    rw [Nat.log2_eq_iff hne]
    constructor
    · have : 2 ^ (Nat.log2 w + k) = 2 ^ k * 2 ^ Nat.log2 w := by rw [Nat.pow_add, Nat.mul_comm]
      rw [this]
      have := Nat.mul_le_mul_left (2 ^ k) h1
      omega
    · have e : 2 ^ (Nat.log2 w + k + 1) = 2 ^ k * 2 ^ (Nat.log2 w + 1) := by
        rw [show Nat.log2 w + k + 1 = k + (Nat.log2 w + 1) by omega, Nat.pow_add]
      rw [e]
      have := Nat.mul_le_mul_left (2 ^ k) (show w + 1 ≤ 2 ^ (Nat.log2 w + 1) from h2)
      rw [Nat.mul_add] at this
      omega
  omega

theorem bitLen_word (w : Nat) (hw : w < 2 ^ 64) (hw0 : w ≠ 0) : 63 - Janus.Arm64.clzNat 64 w + 1 = bitLen w := by
  have h := Fv256.Util.clz_bl 64 w hw
  have hc := (Fv256.B.clz_norm w hw0 hw).1
  omega

theorem bitLen_lt (e : Nat) : e < 2 ^ bitLen e := by
  unfold bitLen
  split
  · rename_i h; subst h; decide
  · exact Nat.lt_log2_self

theorem bitLen_pow_le (e : Nat) (h : bitLen e ≠ 0) : 2 ^ (bitLen e - 1) ≤ e := by
  have he : e ≠ 0 := by intro hc; subst hc; exact h rfl
  have : bitLen e = Nat.log2 e + 1 := by unfold bitLen; rw [if_neg he]
  rw [this]
  simpa using Nat.log2_self_le he


theorem n_top3 (e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (h3 : e3 < 2 ^ 64) (hz : e3 ≠ 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) = 63 - Janus.Arm64.clzNat 64 e3 + 193 := by
  have := bitLen_shift (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2) 192 e3 (by omega) hz
  have e : e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 = e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3 := rfl
  rw [this, ← bitLen_word e3 h3 hz]

theorem n_top2 (e0 e1 e2 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (hz : e2 ≠ 0) :
    bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2) = 63 - Janus.Arm64.clzNat 64 e2 + 129 := by
  have := bitLen_shift (e0 + 2 ^ 64 * e1) 128 e2 (by omega) hz
  rw [this, ← bitLen_word e2 h2 hz]

theorem n_top1 (e0 e1 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (hz : e1 ≠ 0) :
    bitLen (e0 + 2 ^ 64 * e1) = 63 - Janus.Arm64.clzNat 64 e1 + 65 := by
  have := bitLen_shift e0 64 e1 h0 hz
  rw [this, ← bitLen_word e1 h1 hz]

theorem n_top0 (e0 : Nat) (h0 : e0 < 2 ^ 64) (hz : e0 ≠ 0) :
    bitLen e0 = 63 - Janus.Arm64.clzNat 64 e0 + 1 := (bitLen_word e0 h0 hz).symm

theorem bitLen_le (e k : Nat) (h : e < 2 ^ k) : bitLen e ≤ k := by
  unfold bitLen
  split
  · omega
  · rename_i hz
    have := (Nat.log2_lt hz).2 h
    omega

theorem toInt_add_small (a c : Nat) (h : a + c < 2 ^ 62) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 c).toInt = ((a + c : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ge256_of_bitLen (E : Nat) (h : 8 < bitLen E) : 256 ≤ E := by
  have := bitLen_pow_le E (by omega)
  have h2 : 2 ^ 8 ≤ 2 ^ (bitLen E - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem even_of_lsb (b0 : Nat) (h : ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 b0)).getLsbD 0 = true) : b0 % 2 = 0 := by
  rw [Fv256.F.lsb_w32] at h
  simpa using h

theorem early3 (b0 b1 b2 b3 e0 e1 e2 e3 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64) (h3 : e3 < 2 ^ 64)
    (hz : e3 ≠ 0) (hB : b0 % 2 = 0)
    (hbl : ¬ (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e3) + 193#64).toInt ≤ 8) :
    0 = expSpec (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) := by
  have hc := (Fv256.B.clz_norm e3 hz h3).1
  have := toInt_add_small (63 - Janus.Arm64.clzNat 64 e3) 193 (by omega)
  have e193 : (193#64 : BitVec 64) = BitVec.ofNat 64 193 := rfl
  rw [e193, this] at hbl
  have hn := n_top3 e0 e1 e2 e3 h0 h1 h2 h3 hz
  have := ge256_of_bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2 + 2 ^ 192 * e3) (by omega)
  unfold expSpec
  exact (even_exp_zero _ _ (by omega) this).symm

theorem early2 (b0 b1 b2 b3 e0 e1 e2 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64) (h2 : e2 < 2 ^ 64)
    (hz : e2 ≠ 0) (hB : b0 % 2 = 0)
    (hbl : ¬ (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e2) + 129#64).toInt ≤ 8) :
    0 = expSpec (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2) := by
  have hc := (Fv256.B.clz_norm e2 hz h2).1
  have := toInt_add_small (63 - Janus.Arm64.clzNat 64 e2) 129 (by omega)
  have ec : (129#64 : BitVec 64) = BitVec.ofNat 64 129 := rfl
  rw [ec, this] at hbl
  have hn := n_top2 e0 e1 e2 h0 h1 h2 hz
  have := ge256_of_bitLen (e0 + 2 ^ 64 * e1 + 2 ^ 128 * e2) (by omega)
  unfold expSpec
  exact (even_exp_zero _ _ (by omega) this).symm

theorem early1 (b0 b1 b2 b3 e0 e1 : Nat) (h0 : e0 < 2 ^ 64) (h1 : e1 < 2 ^ 64)
    (hz : e1 ≠ 0) (hB : b0 % 2 = 0)
    (hbl : ¬ (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e1) + 65#64).toInt ≤ 8) :
    0 = expSpec (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) (e0 + 2 ^ 64 * e1) := by
  have hc := (Fv256.B.clz_norm e1 hz h1).1
  have := toInt_add_small (63 - Janus.Arm64.clzNat 64 e1) 65 (by omega)
  have ec : (65#64 : BitVec 64) = BitVec.ofNat 64 65 := rfl
  rw [ec, this] at hbl
  have hn := n_top1 e0 e1 h0 h1 hz
  have := ge256_of_bitLen (e0 + 2 ^ 64 * e1) (by omega)
  unfold expSpec
  exact (even_exp_zero _ _ (by omega) this).symm

theorem early0 (b0 b1 b2 b3 e0 : Nat) (h0 : e0 < 2 ^ 64) (hB : b0 % 2 = 0) (K : BitVec 64)
    (hbl : ¬ ((if e0 = 0 then 18446744073709551615#64 else if e0 = 0 then K else BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e0)) + 1#64).toInt ≤ 8) :
    0 = expSpec (b0 + 2 ^ 64 * b1 + 2 ^ 128 * b2 + 2 ^ 192 * b3) e0 := by
  by_cases hz : e0 = 0
  · rw [if_pos hz] at hbl
    exact absurd (by decide) hbl
  · rw [if_neg hz, if_neg hz] at hbl
    have hc := (Fv256.B.clz_norm e0 hz h0).1
    have := toInt_add_small (63 - Janus.Arm64.clzNat 64 e0) 1 (by omega)
    have ec : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
    rw [ec, this] at hbl
    have hn := n_top0 e0 h0 hz
    have := ge256_of_bitLen e0 (by omega)
    unfold expSpec
    exact (even_exp_zero _ _ (by omega) this).symm

theorem nbv0 (e0 : Nat) (h0 : e0 < 2 ^ 64) (K : BitVec 64) :
    ((if e0 = 0 then 18446744073709551615#64 else if e0 = 0 then K else BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e0)) + 1#64)
      = BitVec.ofNat 64 (bitLen e0) := by
  by_cases hz : e0 = 0
  · subst hz
    simp [bitLen]
  · rw [if_neg hz, if_neg hz, n_top0 e0 h0 hz]
    exact (BitVec.ofNat_add _ _).symm

theorem nmem0 (e0 : Nat) (h0 : e0 < 2 ^ 64) (K : BitVec 64) :
    ((if e0 = 0 then 18446744073709551615#64 else if e0 = 0 then K else BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e0)).toNat + 1) % 256 ^ 8
      = bitLen e0 := by
  by_cases hz : e0 = 0
  · subst hz
    simp [bitLen]
  · rw [if_neg hz, if_neg hz, BitVec.toNat_ofNat]
    have hc := (Fv256.B.clz_norm e0 hz h0).1
    have := n_top0 e0 h0 hz
    have h64 : 63 - Janus.Arm64.clzNat 64 e0 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h64]
    have : bitLen e0 < 256 ^ 8 := by omega
    omega

theorem nbvk (a c : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 c = BitVec.ofNat 64 (a + c) := (BitVec.ofNat_add _ _).symm

theorem nmemk (a c : Nat) (h : a + c < 256 ^ 8) : (a + c) % 256 ^ 8 = a + c := Nat.mod_eq_of_lt h

theorem contra_big (e c : Nat) (hc : 8 < c) (hc2 : c < 2 ^ 20) (hb : e < 2 ^ 64)
    (h : (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 e) + BitVec.ofNat 64 c).toInt ≤ 8) : False := by
  have hcl : 63 - Janus.Arm64.clzNat 64 e ≤ 63 := by omega
  rw [toInt_add_small _ _ (by omega)] at h
  omega

end Fv256.F
