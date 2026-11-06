import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB

namespace Fv256.D

theorem f64_bits (q r t Y y0 y1 y2 y3 : Nat) (ht1 : 12 ≤ t) (ht2 : t ≤ 203) (hr : r < 2 ^ t) (hq : q < 2 ^ 52)
    (hY : Y = q * 2 ^ 204 + r * 2 ^ (204 - t))
    (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Y) :
    y3 / 4096 = q ∧
    (2048 ≤ y3 % 4096 ↔ 2 ^ (t - 1) ≤ r) ∧
    ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ r % 2 ^ (t - 1) ≠ 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hh : 2 ^ s * 2 ^ (204 - (s + 1)) = 2 ^ 203 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hr2 : r < 2 * 2 ^ s := by rw [Nat.pow_succ] at hr; omega
  clear hr
  generalize 2 ^ s = h at *
  generalize 2 ^ (204 - (s + 1)) = Pm at *
  have hp : 0 < Pm := by
    rcases Nat.eq_zero_or_pos Pm with h | h
    · subst h; simp at hh
    · exact h
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · subst h'; simp at hh
    · exact h'
  have hu : r * Pm < 2 ^ 204 := by
    have : r * Pm < 2 * h * Pm := Nat.mul_lt_mul_of_pos_right hr2 hp
    have e : 2 * h * Pm = 2 ^ 204 := by rw [Nat.mul_assoc, hh]
    omega
  generalize hU : r * Pm = u at *
  have e3 : y3 = Y / 2 ^ 192 := by omega
  have eY : y3 / 4096 = q ∧ y3 % 4096 = u / 2 ^ 192 := by omega
  refine ⟨eY.1, ?_, ?_⟩
  · rw [eY.2]
    have : 2048 ≤ u / 2 ^ 192 ↔ 2 ^ 203 ≤ u := by omega
    rw [this, ← hh, ← hU]
    exact Nat.mul_le_mul_right_iff hp
  · have : (y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ u % 2 ^ 203 ≠ 0 := by omega
    rw [this, ← hh, ← hU, Nat.mul_mod_mul_right]
    constructor
    · intro hne hz; apply hne; rw [hz]; simp
    · intro hne hz; apply hne
      rcases Nat.mul_eq_zero.1 hz with h | h
      · exact h
      · omega

set_option maxRecDepth 100000 in
open Janus.Float in
theorem f64_nearest (V bl y0 y1 y2 y3 : Nat) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V) (hbl : Spec.bitLen V = bl)
    (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256) :
    Fv256.B.float64BitsNearest V =
      (if (if 2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)
          then y3 / 4096 + 1 else y3 / 4096) / 2 ^ 52 ≠ 0
        then (bl + 1023) * 2 ^ 52
        else (bl + 1022) * 2 ^ 52 +
          (if 2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)
            then y3 / 4096 + 1 else y3 / 4096)) := by
  have hV0 : V ≠ 0 := by have := Nat.two_pow_pos 64; omega
  obtain ⟨hb1, hb2⟩ := Util.bitLen_bounds V hV0
  rw [hbl] at hb1 hb2
  have hbl64 : 64 < bl := by
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ bl ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨L, rfl⟩ : ∃ L, bl = L + 1 := ⟨bl - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hb1
  have hL64 : 64 ≤ L := by omega
  have hL255 : L ≤ 255 := by
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 256 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = L - 52 := ⟨_, rfl⟩
  have ht12 : 12 ≤ t := by omega
  have ht203 : t ≤ 203 := by omega
  have hLt : L = t + 52 := by omega
  -- decomposition
  have h2L : 0 < 2 ^ t := Nat.two_pow_pos t
  have hWdef : V = 2 ^ L + V % 2 ^ L := by
    have : V / 2 ^ L = 1 := by
      apply Nat.le_antisymm
      · have : V / 2 ^ L < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos L)).2 (by rw [Nat.pow_succ] at hb2; omega)
        omega
      · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos L)).2 (by omega)
    have := Nat.div_add_mod V (2 ^ L)
    rw [‹V / 2 ^ L = 1›] at this
    omega
  have hWlt : V % 2 ^ L < 2 ^ L := Nat.mod_lt _ (Nat.two_pow_pos L)
  have hq : V % 2 ^ L / 2 ^ t < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul h2L, ← Nat.pow_add]; rw [show 52 + t = L by omega]; exact hWlt
  have hrW : V % 2 ^ L % 2 ^ t = V % 2 ^ t := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  have hk : V / 2 ^ t = 2 ^ 52 + V % 2 ^ L / 2 ^ t := by
    have e : 2 ^ L = 2 ^ 52 * 2 ^ t := by rw [← Nat.pow_add]; congr 1; omega
    have e5 : V = V % 2 ^ L + 2 ^ t * 2 ^ 52 := by omega
    calc V / 2 ^ t = (V % 2 ^ L + 2 ^ t * 2 ^ 52) / 2 ^ t := by rw [← e5]
      _ = _ := by rw [Nat.add_mul_div_left _ _ h2L]; omega
  have hr : V % 2 ^ t < 2 ^ t := Nat.mod_lt _ h2L
  have hY : V * 2 ^ (257 - (L + 1)) % 2 ^ 256 = V % 2 ^ L / 2 ^ t * 2 ^ 204 + V % 2 ^ t * 2 ^ (204 - t) := by
    have e1 : 257 - (L + 1) = 256 - L := by omega
    rw [e1]
    have e2 : V % 2 ^ L * 2 ^ (256 - L) < 2 ^ 256 := by
      calc V % 2 ^ L * 2 ^ (256 - L) < 2 ^ L * 2 ^ (256 - L) := Nat.mul_lt_mul_of_pos_right hWlt (Nat.two_pow_pos _)
        _ = 2 ^ 256 := by rw [← Nat.pow_add]; congr 1; omega
    have e3 : V * 2 ^ (256 - L) = 2 ^ 256 + V % 2 ^ L * 2 ^ (256 - L) := by
      calc V * 2 ^ (256 - L) = (2 ^ L + V % 2 ^ L) * 2 ^ (256 - L) := by rw [← hWdef]
        _ = _ := by rw [Nat.add_mul, ← Nat.pow_add, show L + (256 - L) = 256 by omega]
    rw [e3, Nat.add_mod_left, Nat.mod_eq_of_lt e2]
    have e4 : V % 2 ^ L = V % 2 ^ L / 2 ^ t * 2 ^ t + V % 2 ^ t := by
      have := Nat.div_add_mod (V % 2 ^ L) (2 ^ t)
      rw [hrW, Nat.mul_comm (2 ^ t)] at this; omega
    calc V % 2 ^ L * 2 ^ (256 - L) = (V % 2 ^ L / 2 ^ t * 2 ^ t + V % 2 ^ t) * 2 ^ (256 - L) := by rw [← e4]
      _ = _ := by rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, show t + (256 - L) = 204 by omega, show 256 - L = 204 - t by omega]
  have hbits := f64_bits (V % 2 ^ L / 2 ^ t) (V % 2 ^ t) t (V * 2 ^ (257 - (L + 1)) % 2 ^ 256) y0 y1 y2 y3 ht12 ht203 hr hq hY h0 h1 h2 h3 hy
  obtain ⟨hb_q, hb_rnd, hb_st⟩ := hbits
  have hR : (roundAt RM.rne false V 0 ((L : Int) - 52)).1 =
      (if roundUp RM.rne false (V / 2 ^ t) (V % 2 ^ t) t = true then V / 2 ^ t + 1 else V / 2 ^ t) := by
    unfold roundAt
    rw [if_neg (by omega)]
    have : ((L : Int) - 52 - 0).toNat = t := by omega
    simp only [this]
  unfold Fv256.B.float64BitsNearest
  rw [fromInt_b64_big .rne V L hb1 hb2 (by omega) (by omega), hR]
  have hh : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hhpos : 0 < 2 ^ (t - 1) := Nat.two_pow_pos _
  generalize 2 ^ (t - 1) = h at *
  have hmod : V % 2 ^ t % h = if h ≤ V % 2 ^ t then V % 2 ^ t - h else V % 2 ^ t := by
    split
    · rw [Nat.mod_eq_sub_mod ‹_›, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hRU : roundUp RM.rne false (V / 2 ^ t) (V % 2 ^ t) t = true ↔
      (2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)) := by
    unfold roundUp
    rw [hb_rnd, hb_st, hb_q, hk]
    simp only [Nat.add_mod_left, hmod]
    generalize V % 2 ^ t = r at *
    generalize V % 2 ^ L / 2 ^ t = q at *
    by_cases a : r = 0 <;> by_cases b : h ≤ r <;> simp [a, b] <;> omega
  unfold pack
  rw [Janus.Float.b64_fbits]
  have e53 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by decide
  have hk' : V / 2 ^ t = 2 ^ 52 + y3 / 4096 := by rw [hk, hb_q]
  rw [e53, hk']
  rw [hk'] at hRU
  by_cases hC : (2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1))
  · simp only [if_pos (hRU.2 hC), if_pos hC, Bool.false_eq_true, ite_false]
    split <;> split <;> omega
  · simp only [if_neg (fun h => hC (hRU.1 h)), if_neg hC, Bool.false_eq_true, ite_false]
    split <;> split <;> omega

end Fv256.D
