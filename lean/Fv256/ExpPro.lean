import Fv256.UdivMathB
import Fv256.ExpFinal
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

end Fv256.F
