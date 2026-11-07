import Fv256.RecipMath

namespace Fv256.RecipMath

/-! # Recip stages: closed-form windows (Extracted-free) -/


/-- stage 2 closed form: `e = a2h·y3 + (⌊a2l·y2 / 2^64⌋ + a2l·y3 + a2h·y2) / 2^64`, `a2 = r1²` -/
def stage2e (r1 y2 y3 : Nat) : Nat :=
  r1 * r1 / 2 ^ 64 * y3 + ((r1 * r1 % 2 ^ 64 * y2) / 2 ^ 64 + r1 * r1 % 2 ^ 64 * y3 + r1 * r1 / 2 ^ 64 * y2) / 2 ^ 64

theorem stage2e_win (r1 y0 y1 y2 y3 : Nat) (hr : r1 < 2 ^ 64) (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64) :
    2 ^ 256 * stage2e r1 y2 y3 ≤ r1 * r1 * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) ∧
    r1 * r1 * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) < 2 ^ 256 * stage2e r1 y2 y3 + 3 * 2 ^ 256 := by
  unfold stage2e
  have hdm := Nat.div_add_mod (r1 * r1) (2 ^ 64)
  have hlt := Nat.mod_lt (r1 * r1) (Nat.two_pow_pos 64)
  generalize r1 * r1 / 2 ^ 64 = ah at *
  generalize r1 * r1 % 2 ^ 64 = al at *
  have hP := Nat.div_add_mod (al * y2) (2 ^ 64)
  have hPl := Nat.mod_lt (al * y2) (Nat.two_pow_pos 64)
  generalize (al * y2) / 2 ^ 64 = hiP at *
  generalize (al * y2) % 2 ^ 64 = loP at *
  have hT := Nat.div_add_mod (hiP + al * y3 + ah * y2) (2 ^ 64)
  have hTl := Nat.mod_lt (hiP + al * y3 + ah * y2) (Nat.two_pow_pos 64)
  generalize (hiP + al * y3 + ah * y2) / 2 ^ 64 = tq at *
  generalize (hiP + al * y3 + ah * y2) % 2 ^ 64 = tr at *
  have hr2 : r1 * r1 < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' hr hr
    simpa [← Nat.pow_add] using this
  have hyr : y0 + 2 ^ 64 * y1 < 2 ^ 128 := by
    have : 2 ^ 64 * y1 ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ 64 * (2 ^ 64 - 1) + 2 ^ 64 = 2 ^ 128 := by decide
    omega
  have hprod : r1 * r1 * (y0 + 2 ^ 64 * y1) < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' hr2 hyr
  have id1 : r1 * r1 * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) =
      2 ^ 256 * (ah * y3 + tq) + 2 ^ 128 * (loP + 2 ^ 64 * tr) + r1 * r1 * (y0 + 2 ^ 64 * y1) := by
    rw [← hdm]
    have hT' : hiP + al * y3 + ah * y2 = 2 ^ 64 * tq + tr := hT.symm
    grind
  have hlo : loP + 2 ^ 64 * tr < 2 ^ 128 := by
    have : 2 ^ 64 * tr ≤ 2 ^ 64 * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ 64 * (2 ^ 64 - 1) + 2 ^ 64 = 2 ^ 128 := by decide
    omega
  have hm : 2 ^ 128 * (loP + 2 ^ 64 * tr) < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul_of_pos_left hlo (Nat.two_pow_pos 128)
  rw [id1]
  have e256 : 2 ^ 128 * 2 ^ 128 = 2 ^ 256 := by decide
  have e3 : 3 * 2 ^ 256 = 2 ^ 256 + 2 * 2 ^ 256 := by omega
  constructor <;> omega



/-- stage 3: the sum of word products the code accumulates in `q0..q4` (pairs `i + j ≥ 3` in full, the three `i + j = 2` pairs by their high words) -/
def stage3q (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) : Nat :=
  x2 * y0 / 2 ^ 64 + x1 * y1 / 2 ^ 64 + x0 * y2 / 2 ^ 64 + (x3 * y0 + x2 * y1 + x1 * y2 + x0 * y3) +
    2 ^ 64 * (x3 * y1 + x2 * y2 + x1 * y3) + 2 ^ 128 * (x3 * y2 + x2 * y3) + 2 ^ 192 * (x3 * y3)

theorem stage3q_win (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) (hx0 : x0 < 2 ^ 64) (hx1 : x1 < 2 ^ 64) (hx2 : x2 < 2 ^ 64)
    (hx3 : x3 < 2 ^ 64) (hy0 : y0 < 2 ^ 64) (hy1 : y1 < 2 ^ 64) (hy2 : y2 < 2 ^ 64) (hy3 : y3 < 2 ^ 64) :
    2 ^ 192 * stage3q x0 x1 x2 x3 y0 y1 y2 y3 ≤
      (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) ∧
    (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) <
      2 ^ 192 * stage3q x0 x1 x2 x3 y0 y1 y2 y3 + 6 * 2 ^ 192 := by
  unfold stage3q
  have h20 := Nat.div_add_mod (x2 * y0) (2 ^ 64)
  have h11 := Nat.div_add_mod (x1 * y1) (2 ^ 64)
  have h02 := Nat.div_add_mod (x0 * y2) (2 ^ 64)
  have l20 := Nat.mod_lt (x2 * y0) (Nat.two_pow_pos 64)
  have l11 := Nat.mod_lt (x1 * y1) (Nat.two_pow_pos 64)
  have l02 := Nat.mod_lt (x0 * y2) (Nat.two_pow_pos 64)
  generalize x2 * y0 / 2 ^ 64 = a20 at *
  generalize x1 * y1 / 2 ^ 64 = a11 at *
  generalize x0 * y2 / 2 ^ 64 = a02 at *
  generalize x2 * y0 % 2 ^ 64 = b20 at *
  generalize x1 * y1 % 2 ^ 64 = b11 at *
  generalize x0 * y2 % 2 ^ 64 = b02 at *
  have p00 : x0 * y0 < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' hx0 hy0
    simpa [← Nat.pow_add] using this
  have p01 : x0 * y1 < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' hx0 hy1
    simpa [← Nat.pow_add] using this
  have p10 : x1 * y0 < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' hx1 hy0
    simpa [← Nat.pow_add] using this
  have id1 : (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) =
      2 ^ 192 * (a20 + a11 + a02 + (x3 * y0 + x2 * y1 + x1 * y2 + x0 * y3) +
        2 ^ 64 * (x3 * y1 + x2 * y2 + x1 * y3) + 2 ^ 128 * (x3 * y2 + x2 * y3) + 2 ^ 192 * (x3 * y3)) +
      (x0 * y0 + 2 ^ 64 * (x0 * y1 + x1 * y0) + 2 ^ 128 * (b20 + b11 + b02)) := by
    grind
  rw [id1]
  have e1 : 2 ^ 64 * (x0 * y1 + x1 * y0) < 2 ^ 64 * 2 ^ 129 :=
    Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos 64)
  have e2 : 2 ^ 128 * (b20 + b11 + b02) < 2 ^ 128 * (3 * 2 ^ 64) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos 128)
  have c1 : 2 ^ 64 * 2 ^ 129 = 2 ^ 193 := by decide
  have c2 : 2 ^ 128 * (3 * 2 ^ 64) = 3 * 2 ^ 192 := by decide
  have c3 : 2 ^ 193 = 2 * 2 ^ 192 := by decide
  have c4 : 2 ^ 128 < 2 ^ 192 := by decide
  constructor <;> omega



theorem T2win (r1 e Y : Int) (h : 2 ^ 256 * e ≤ r1 * r1 * Y ∧ r1 * r1 * Y < 2 ^ 256 * e + 3 * 2 ^ 256) :
    -(8 * 2 ^ 383) ≤ 2 ^ 383 * (2 * e) - (r1 * 2 ^ 64) * (r1 * 2 ^ 64) * Y ∧
    2 ^ 383 * (2 * e) - (r1 * 2 ^ 64) * (r1 * 2 ^ 64) * Y ≤ 8 * 2 ^ 383 := by
  have id : (r1 * 2 ^ 64) * (r1 * 2 ^ 64) * Y = 2 ^ 128 * (r1 * r1 * Y) := by grind
  have e1 : 2 ^ 383 * (2 * e) = 2 ^ 128 * (2 ^ 256 * e) := by grind
  rw [id, e1]
  generalize r1 * r1 * Y = P at *
  generalize (2 : Int) ^ 256 * e = E at *
  constructor <;> omega

theorem T3win (r2 K Y q : Int) (hq : 2 ^ 192 * q ≤ r2 * r2 * Y ∧ r2 * r2 * Y < 2 ^ 192 * q + 6 * 2 ^ 192)
    (hK : (K - 1) * 2 ^ 128 < q ∧ q ≤ K * 2 ^ 128) :
    -(8 * 2 ^ 447) ≤ 2 ^ 447 * (2 * K) - (r2 * 2 ^ 64) * (r2 * 2 ^ 64) * Y ∧
    2 ^ 447 * (2 * K) - (r2 * 2 ^ 64) * (r2 * 2 ^ 64) * Y ≤ 8 * 2 ^ 447 := by
  have id : (r2 * 2 ^ 64) * (r2 * 2 ^ 64) * Y = 2 ^ 128 * (r2 * r2 * Y) := by grind
  have e1 : 2 ^ 447 * (2 * K) = 2 ^ 128 * (2 ^ 320 * K) := by grind
  rw [id, e1]
  have g1 : 2 ^ 192 * q ≤ 2 ^ 192 * (K * 2 ^ 128) := Int.mul_le_mul_of_nonneg_left hK.2 (by omega)
  have g2 : 2 ^ 192 * ((K - 1) * 2 ^ 128) < 2 ^ 192 * q := Int.mul_lt_mul_of_pos_left hK.1 (by omega)
  have f1 : (2 : Int) ^ 192 * (K * 2 ^ 128) = 2 ^ 320 * K := by grind
  have f2 : (2 : Int) ^ 192 * ((K - 1) * 2 ^ 128) = 2 ^ 320 * K - 2 ^ 320 := by grind
  rw [f1] at g1
  rw [f2] at g2
  generalize r2 * r2 * Y = P at *
  generalize (2 : Int) ^ 320 * K = W at *
  generalize (2 : Int) ^ 192 * q = Q at *
  constructor <;> omega



/-- power-of-two `m`: the library returns `2^(512-i) - 1`, which is `⌊(2^512-1)/m⌋` -/
theorem pow2_mu (i : Nat) (h : i ≤ 512) : (2 ^ 512 - 1) / 2 ^ i = 2 ^ (512 - i) - 1 := by
  have e : 2 ^ i * 2 ^ (512 - i) = 2 ^ 512 := by rw [← Nat.pow_add]; congr 1; omega
  have ha := Nat.two_pow_pos i
  have hb := Nat.two_pow_pos (512 - i)
  generalize 2 ^ i = a at *
  generalize 2 ^ (512 - i) = b at *
  rw [← e]
  apply Nat.div_eq_of_lt_le
  · have : (b - 1) * a = a * b - a := by
      rw [Nat.mul_comm, Nat.mul_sub, Nat.mul_one]
    have h2 : a * b ≥ a := Nat.le_mul_of_pos_right a hb
    omega
  · have : b * a = a * b := Nat.mul_comm _ _
    have h2 : a * b ≥ a := Nat.le_mul_of_pos_right a hb
    have h3 : (b - 1 + 1) * a = b * a := by rw [Nat.sub_add_cancel hb]
    omega

/-- stage 1 (`yh = 2^31`): the doubled value does not wrap for `y3 > 2^63` -/
theorem stage1_top (y3 : Nat) (h1 : 2 ^ 63 < y3) (h2 : y3 < 2 ^ 63 + 2 ^ 32) :
    (2 ^ 32 - 1) * (2 ^ 32 - 1) * y3 / 2 ^ 64 > 2 ^ 63 - 2 ^ 32 := by
  apply Nat.lt_of_succ_le
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos 64)).2
  omega



theorem mul_lt_of (a b A B : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a < A) (h2 : b < B) : a * b < A * B := by
  have h3 : a * b ≤ a * B := Int.mul_le_mul_of_nonneg_left (by omega) ha
  have h4 : a * B < A * B := Int.mul_lt_mul_of_pos_right h1 (by omega)
  omega

theorem d0win (r0 yh yl y : Int) (hy : y = yh * 2 ^ 224 + yl) (hyl : 0 ≤ yl ∧ yl < 2 ^ 224)
    (hyh : 2 ^ 31 ≤ yh ∧ yh < 2 ^ 32) (hr0 : 0 ≤ r0 ∧ r0 < 2 ^ 32)
    (hq : (r0 * yh ≤ 2 ^ 63 ∧ 2 ^ 63 < r0 * yh + yh) ∨ (yh = 2 ^ 31 ∧ r0 = 2 ^ 32 - 1)) :
    -(2 ^ 288) ≤ 2 ^ 319 - (r0 * 2 ^ 32) * y ∧ 2 ^ 319 - (r0 * 2 ^ 32) * y ≤ 2 ^ 288 := by
  have e1 : (r0 * 2 ^ 32) * y = 2 ^ 256 * (r0 * yh) + 2 ^ 32 * (r0 * yl) := by subst hy; grind
  have hb : r0 * yl < 2 ^ 32 * 2 ^ 224 := mul_lt_of r0 yl _ _ hr0.1 hyl.1 hr0.2 hyl.2
  have c1 : (2 : Int) ^ 32 * 2 ^ 224 = 2 ^ 256 := by decide
  have hnn : 0 ≤ r0 * yl := Int.mul_nonneg hr0.1 hyl.1
  have c2 : (2 : Int) ^ 319 = 2 ^ 256 * 2 ^ 63 := by decide
  rw [e1, c2]
  have hb2 : 2 ^ 32 * (r0 * yl) < 2 ^ 32 * 2 ^ 256 := by
    have := Int.mul_lt_mul_of_pos_left (show r0 * yl < 2 ^ 256 by omega) (show (0 : Int) < 2 ^ 32 by omega)
    exact this
  have hb3 : 0 ≤ 2 ^ 32 * (r0 * yl) := Int.mul_nonneg (by omega) hnn
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have g1 : 2 ^ 256 * (r0 * yh) ≤ 2 ^ 256 * 2 ^ 63 := Int.mul_le_mul_of_nonneg_left h1 (by omega)
    have g2 : 2 ^ 256 * 2 ^ 63 < 2 ^ 256 * (r0 * yh + yh) := Int.mul_lt_mul_of_pos_left h2 (by omega)
    have g3 : 2 ^ 256 * yh < 2 ^ 256 * 2 ^ 32 := Int.mul_lt_mul_of_pos_left hyh.2 (by omega)
    have g4 : 2 ^ 256 * (r0 * yh + yh) = 2 ^ 256 * (r0 * yh) + 2 ^ 256 * yh := by grind
    have c3 : (2 : Int) ^ 256 * 2 ^ 32 = 2 ^ 288 := by decide
    have c4 : (2 : Int) ^ 32 * 2 ^ 256 = 2 ^ 288 := by decide
    constructor <;> omega
  · subst h1 h2
    have c3 : (2 : Int) ^ 256 * (((2 : Int) ^ 32 - 1) * 2 ^ 31) = 2 ^ 256 * 2 ^ 63 - 2 ^ 256 * 2 ^ 31 := by decide
    have c4 : (2 : Int) ^ 32 * 2 ^ 256 = 2 ^ 288 := by decide
    have c5 : (2 : Int) ^ 256 * 2 ^ 31 < 2 ^ 288 := by decide
    constructor <;> omega

theorem T1win (r0 y3 yy y t1 : Int) (hy : y = y3 * 2 ^ 192 + yy) (hyy : 0 ≤ yy ∧ yy < 2 ^ 192)
    (hr0 : 0 ≤ r0 ∧ r0 < 2 ^ 32) (hy3 : 0 ≤ y3)
    (ht : 2 ^ 64 * t1 ≤ r0 * r0 * y3 ∧ r0 * r0 * y3 < 2 ^ 64 * t1 + 2 ^ 64) :
    -(8 * 2 ^ 319) ≤ 2 ^ 319 * (2 * t1) - (r0 * 2 ^ 32) * (r0 * 2 ^ 32) * y ∧
    2 ^ 319 * (2 * t1) - (r0 * 2 ^ 32) * (r0 * 2 ^ 32) * y ≤ 8 * 2 ^ 319 := by
  have e1 : (r0 * 2 ^ 32) * (r0 * 2 ^ 32) * y = 2 ^ 64 * (r0 * r0 * y3) * 2 ^ 192 + 2 ^ 64 * (r0 * r0 * yy) := by
    subst hy; grind
  have e2 : 2 ^ 319 * (2 * t1) = 2 ^ 256 * (2 ^ 64 * t1) := by grind
  have hrr : r0 * r0 < 2 ^ 32 * 2 ^ 32 := mul_lt_of r0 r0 _ _ hr0.1 hr0.1 hr0.2 hr0.2
  have hrr0 : 0 ≤ r0 * r0 := Int.mul_nonneg hr0.1 hr0.1
  have hyy2 : r0 * r0 * yy < 2 ^ 32 * 2 ^ 32 * 2 ^ 192 := mul_lt_of _ _ _ _ hrr0 hyy.1 hrr hyy.2
  have hyy0 : 0 ≤ r0 * r0 * yy := Int.mul_nonneg hrr0 hyy.1
  rw [e1, e2]
  have g1 : 2 ^ 256 * (2 ^ 64 * t1) ≤ 2 ^ 256 * (r0 * r0 * y3) := Int.mul_le_mul_of_nonneg_left ht.1 (by omega)
  have g2 : 2 ^ 256 * (r0 * r0 * y3) < 2 ^ 256 * (2 ^ 64 * t1 + 2 ^ 64) := Int.mul_lt_mul_of_pos_left ht.2 (by omega)
  have g3 : 2 ^ 256 * (2 ^ 64 * t1 + 2 ^ 64) = 2 ^ 256 * (2 ^ 64 * t1) + 2 ^ 320 := by grind
  have k1 : 2 ^ 64 * (r0 * r0 * y3) * 2 ^ 192 = 2 ^ 256 * (r0 * r0 * y3) := by grind
  have c1 : (2 : Int) ^ 64 * (2 ^ 32 * 2 ^ 32 * 2 ^ 192) = 2 ^ 320 := by decide
  have g4 : 2 ^ 64 * (r0 * r0 * yy) < 2 ^ 64 * (2 ^ 32 * 2 ^ 32 * 2 ^ 192) := Int.mul_lt_mul_of_pos_left hyy2 (by omega)
  have g5 : 0 ≤ 2 ^ 64 * (r0 * r0 * yy) := Int.mul_nonneg (by omega) hyy0
  have c2 : (2 : Int) ^ 320 = 2 * 2 ^ 319 := by decide
  rw [k1]
  generalize 2 ^ 256 * (2 ^ 64 * t1) = U at *
  generalize 2 ^ 256 * (r0 * r0 * y3) = V at *
  generalize 2 ^ 64 * (r0 * r0 * yy) = W at *
  constructor <;> omega


end Fv256.RecipMath
