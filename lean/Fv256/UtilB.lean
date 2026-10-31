import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB

/-! Helper lemmas for family B (division, modular arithmetic, iterative numerics). -/

namespace Fv256.B

theorem clz_cases (v : Nat) (h : v < 2 ^ 64) : v = 0 ∨ Janus.Arm64.clzNat 64 v < 64 := by
  by_cases hv : v = 0
  · exact Or.inl hv
  · refine Or.inr ?_
    have := Fv256.Util.clz_bl 64 v h
    have h2 : 0 < Fv256.Spec.bitLen v := by
      unfold Fv256.Spec.bitLen; rw [if_neg hv]; omega
    omega

end Fv256.B

namespace Fv256.B

theorem append_toNat (E F : BitVec 64) : (E ++ F).toNat = E.toNat * 2 ^ 64 + F.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt F.isLt, Nat.shiftLeft_eq]

theorem extract12_append (E F : BitVec 64) :
    (BitVec.extractLsb' 12 64 (E ++ F)).toNat = (E.toNat * 2 ^ 64 + F.toNat) / 2 ^ 12 % 2 ^ 64 := by
  have h := append_toNat E F
  simp [BitVec.extractLsb'_eq_extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow, h]

theorem writeLE_same (m : Janus.Arm64.Memory) (a n v w : Nat) :
    (m.writeLE a n v).writeLE a n w = m.writeLE a n w := by
  cases m with
  | mk bytes regions =>
  simp only [Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.mk.injEq, and_true]
  funext x
  by_cases h : a ≤ x ∧ x < a + n <;> simp [h]

end Fv256.B

namespace Fv256.B

/-- The number formed by the `n` little-endian 64-bit words at `p` (lowest word first). -/
def wv (m : Janus.Arm64.Memory) (p : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => m.readLE p 8 + 2 ^ 64 * wv m (p + 8) n

theorem wv_lt (m : Janus.Arm64.Memory) (p n : Nat) : wv m p n < 2 ^ (64 * n) := by
  induction n generalizing p with
  | zero => simp [wv]
  | succ n ih =>
    simp only [wv]
    have h1 := Janus.Arm64.Memory.readLE_lt m p 8
    have h2 := ih (p + 8)
    have : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by rw [show 64 * (n + 1) = 64 + 64 * n by omega, Nat.pow_add]
    rw [this]
    simp only [Nat.reducePow] at h1 ⊢
    omega

end Fv256.B

namespace Fv256.B
theorem e1 (B d V e u0 u1 q r S : Int) (hV : V * d + e + 1 = B * B) (hS : S = V * u1 + u0)
    (hT : u1 * B + u0 = q * d + r) : d * (S - B * q) = B * r - (1 + e) * u1 - (B - d) * u0 := by
  grind

-- bounds on Delta = S - B q
theorem mg_bounds (B d e u0 u1 q r S : Int) (hd0 : 0 < d) (hdB : d < B) (hBd : B ≤ 2 * d)
    (he0 : 0 ≤ e) (he : e < d) (hu10 : 0 ≤ u1) (hu1 : u1 < d) (hu00 : 0 ≤ u0) (hu0 : u0 < B)
    (hr0 : 0 ≤ r) (hr : r < d)
    (E : d * (S - B * q) = B * r - (1 + e) * u1 - (B - d) * u0) :
    S - B * q < B ∧ -(2 * B) < S - B * q := by
  have p1 : 0 ≤ (1 + e) * u1 := Int.mul_nonneg (by omega) hu10
  have p2 : 0 ≤ (B - d) * u0 := Int.mul_nonneg (by omega) hu00
  have p3 : (1 + e) * u1 ≤ d * d := Int.mul_le_mul (by omega) (by omega) hu10 (by omega)
  have p4 : (B - d) * u0 ≤ d * B := Int.mul_le_mul (by omega) (by omega) hu00 (by omega)
  have p6 : d * d < d * B := Int.mul_lt_mul_of_pos_left hdB hd0
  have p0 : 0 ≤ B * r := Int.mul_nonneg (by omega) hr0
  have p5 : B * r < B * d := Int.mul_lt_mul_of_pos_left hr (by omega)
  constructor
  · refine Int.lt_of_not_ge (fun h => ?_)
    have : d * B ≤ d * (S - B * q) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    rw [Int.mul_comm B d] at p5
    omega
  · refine Int.lt_of_not_ge (fun h => ?_)
    have : d * (S - B * q) ≤ d * (-(2 * B)) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h2 : d * (-(2 * B)) = -(2 * (d * B)) := by grind
    omega

theorem mg_cases (B d e u0 u1 q r q1 q0 : Int) (hd0 : 0 < d) (hdB : d < B) (hBd : B ≤ 2 * d)
    (he0 : 0 ≤ e) (he : e < d) (hu10 : 0 ≤ u1) (hu1 : u1 < d) (hu00 : 0 ≤ u0) (hu0 : u0 < B)
    (hr0 : 0 ≤ r) (hr : r < d) (hq00 : 0 ≤ q0) (hq0 : q0 < B)
    (E : d * (B * q1 + q0 - B * q) = B * r - (1 + e) * u1 - (B - d) * u0) :
    (q1 = q ∧ q0 < B - d + r) ∨
    (q1 + 1 = q ∧ (r ≤ q0 ∨ (q0 < r ∧ r + d < B))) ∨
    (q1 + 2 = q ∧ r + d ≤ q0 ∧ r + d < B) := by
  have hb := mg_bounds B d e u0 u1 q r (B * q1 + q0) hd0 hdB hBd he0 he hu10 hu1 hu00 hu0 hr0 hr E
  have hk : q1 - q = 0 ∨ q1 - q = -1 ∨ q1 - q = -2 := by
    have h1 : B * (q1 - q) < B * 1 := by
      have : B * (q1 - q) = B * q1 - B * q := by grind
      omega
    have h2 : B * (-3) < B * (q1 - q) := by
      have : B * (q1 - q) = B * q1 - B * q := by grind
      omega
    have h1' : q1 - q < 1 := Int.lt_of_mul_lt_mul_left h1 (by omega)
    have h2' : -3 < q1 - q := Int.lt_of_mul_lt_mul_left h2 (by omega)
    omega
  -- product facts
  have f1 : (1 + e) * u1 ≤ d * (d - 1) := Int.mul_le_mul (by omega) (by omega) hu10 (by omega)
  have f2 : (B - d) * u0 ≤ (B - d) * (B - 1) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
  have f3 : 0 ≤ (1 + e) * u1 := Int.mul_nonneg (by omega) hu10
  have f4 : 0 ≤ (B - d) * u0 := Int.mul_nonneg (by omega) hu00
  have f5 : 0 < (B - d) * (d - r) := Int.mul_pos (by omega) (by omega)
  have f6 : 0 ≤ (B - d) * r := Int.mul_nonneg (by omega) hr0
  have f7 : 0 ≤ (2 * d - B) * (B - d) := Int.mul_nonneg (by omega) (by omega)
  have g1 : d * (d - 1) = d * d - d := by grind
  have g2 : (B - d) * (B - 1) = B * B - B - d * B + d := by grind
  have g3 : (B - d) * (d - r) = B * d - B * r - d * d + d * r := by grind
  have g4 : (B - d) * r = B * r - d * r := by grind
  have g5 : (2 * d - B) * (B - d) = 2 * d * B - 2 * d * d - B * B + B * d := by grind
  have gE : d * (B * q1 + q0 - B * q) = d * (B * (q1 - q) + q0) := by grind
  rcases hk with h | h | h
  · -- k = 0
    left
    have hq1 : q1 = q := by omega
    refine ⟨hq1, ?_⟩
    subst hq1
    have e0 : d * q0 = B * r - (1 + e) * u1 - (B - d) * u0 := by
      have : B * q1 + q0 - B * q1 = q0 := by omega
      rw [this] at E; exact E
    have : d * q0 < d * (B - d + r) := by
      have : d * (B - d + r) = d * B - d * d + d * r := by grind
      grind
    exact Int.lt_of_mul_lt_mul_left this (by omega)
  · -- k = 1
    right; left
    have hq1 : q1 + 1 = q := by omega
    refine ⟨hq1, ?_⟩
    have e0 : d * q0 = d * B + B * r - (1 + e) * u1 - (B - d) * u0 := by
      have : q = q1 + 1 := by omega
      subst this
      have : d * (B * q1 + q0 - B * (q1 + 1)) = d * q0 - d * B := by grind
      omega
    by_cases hlt : q0 < r
    · right
      refine ⟨hlt, Int.lt_of_not_ge (fun hge2 => ?_)⟩
      have a1 : d * q0 < d * r := Int.mul_lt_mul_of_pos_left hlt hd0
      have a2 : (B - d) * (B - d) ≤ (B - d) * r := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have g6 : (B - d) * (B - d) = B * B - 2 * B * d + d * d := by grind
      have g7 : (B - d) * r = B * r - d * r := by grind
      grind
    · left; omega
  · -- k = 2
    right; right
    have hq1 : q1 + 2 = q := by omega
    have e0 : d * q0 = 2 * (d * B) + B * r - (1 + e) * u1 - (B - d) * u0 := by
      have : q = q1 + 2 := by omega
      subst this
      have : d * (B * q1 + q0 - B * (q1 + 2)) = d * q0 - 2 * (d * B) := by grind
      omega
    refine ⟨hq1, ?_, ?_⟩
    · have : d * (r + d) ≤ d * q0 := by
        have : d * (r + d) = d * r + d * d := by grind
        grind
      exact Int.le_of_mul_le_mul_left this hd0
    · refine Int.lt_of_not_ge (fun hge2 => ?_)
      have a1 : d * q0 < d * B := Int.mul_lt_mul_of_pos_left hq0 hd0
      have a2 : B * (B - d) ≤ B * r := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have a3 : d * d < d * B := Int.mul_lt_mul_of_pos_left hdB hd0
      grind


/-- Möller–Granlund 2-by-1 division step (Algorithm 4 of "Improved division by invariant integers"),
over base `B`, as the compiled code performs it (all word arithmetic reduced modulo `B`). -/
def div2by1 (B d v u1 u0 : Nat) : Nat × Nat :=
  let p := v * u1
  let sl := p % B + u0
  let qh := (p / B + u1 + sl / B) % B
  let ql := sl % B
  let q1 := (qh + 1) % B
  let r := (u0 + B - (q1 * d) % B) % B
  let fire := ql < r
  let q1 := if fire then (q1 + B - 1) % B else q1
  let r := if fire then (r + d) % B else r
  if d ≤ r then ((q1 + 1) % B, r - d) else (q1, r)

theorem sub_mod_eq (B c d u0 X : Nat) (hu0 : u0 < B) (hX : X < B) (h : (X + c * d) % B = u0) :
    (u0 + B - (c * d) % B) % B = X := by
  have hm : (c * d) % B < B := Nat.mod_lt _ (by omega)
  have h' : (X + (c * d) % B) % B = u0 := by rw [← h]; simp [Nat.add_mod]
  by_cases hc : X + (c * d) % B < B
  · rw [Nat.mod_eq_of_lt hc] at h'
    have : u0 + B - (c * d) % B = X + B := by omega
    rw [this]; simp [Nat.add_mod_right, Nat.mod_eq_of_lt hX]
  · have : (X + (c * d) % B) % B = X + (c * d) % B - B := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have : u0 + B - (c * d) % B = X := by omega
    rw [this, Nat.mod_eq_of_lt hX]

theorem cong_mul (a B d X : Nat) : ((a % B) * d + X) % B = (a * d + X) % B := by
  simp [Nat.add_mod, Nat.mul_mod]

theorem div2by1_correct (B d V u1 u0 : Nat) (hBd : B ≤ 2 * d) (hdB : d < B)
    (hV : V = (B * B - 1) / d) (hu1 : u1 < d) (hu0 : u0 < B) :
    div2by1 B d (V - B) u1 u0 = ((u1 * B + u0) / d, (u1 * B + u0) % d) := by
  have hd0 : 0 < d := by omega
  have hB0 : 0 < B := by omega
  obtain ⟨e, he⟩ : ∃ e, e = (B * B - 1) % d := ⟨_, rfl⟩
  have hBB : 1 ≤ B * B := Nat.mul_pos hB0 hB0
  have hVe : V * d + e + 1 = B * B := by
    have := Nat.div_add_mod (B * B - 1) d
    rw [← hV, ← he] at this
    rw [Nat.mul_comm V d]; omega
  have hed : e < d := by rw [he]; exact Nat.mod_lt _ hd0
  have hVB : B ≤ V := by
    refine Nat.le_of_not_lt (fun h => ?_)
    have h1 : B * d < B * B := Nat.mul_lt_mul_of_pos_left hdB hB0
    have h2 : (V + 1) * d ≤ B * d := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul] at h2
    omega
  obtain ⟨v, hv⟩ : ∃ v, v = V - B := ⟨_, rfl⟩
  rw [← hv]
  have hVv : V = v + B := by omega
  -- the true quotient and remainder
  obtain ⟨q, hq⟩ : ∃ q, q = (u1 * B + u0) / d := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = (u1 * B + u0) % d := ⟨_, rfl⟩
  have hT : u1 * B + u0 = d * q + r := by
    have := Nat.div_add_mod (u1 * B + u0) d; rw [← hq, ← hr] at this; omega
  have hrd : r < d := by rw [hr]; exact Nat.mod_lt _ hd0
  have hqB : q < B := by
    have : u1 * B + u0 < d * B := by
      have : (u1 + 1) * B ≤ d * B := Nat.mul_le_mul_right _ hu1
      rw [Nat.add_mul] at this; omega
    have : d * q < d * B := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  rw [← hq, ← hr]
  -- S
  obtain ⟨S, hS⟩ : ∃ S, S = V * u1 + u0 := ⟨_, rfl⟩
  have hSB : S < B * B := by
    have h1 : V * u1 ≤ V * (d - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : V * (d - 1) + V = V * d := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  have hSdec : S = B * (v * u1 / B + u1) + (v * u1 % B + u0) := by
    have := Nat.div_add_mod (v * u1) B
    have h3 : V * u1 = v * u1 + B * u1 := by rw [hVv]; grind
    rw [hS, h3]
    calc v * u1 + B * u1 + u0 = (B * (v * u1 / B) + v * u1 % B) + B * u1 + u0 := by rw [this]
      _ = _ := by grind
  have hq1 : (v * u1 / B + u1 + (v * u1 % B + u0) / B) = S / B := by
    rw [hSdec, Nat.mul_add_div hB0]
  have hq0 : (v * u1 % B + u0) % B = S % B := by
    rw [hSdec, Nat.mul_add_mod]
  have hq1B : S / B < B := Nat.div_lt_of_lt_mul hSB
  have hq0B : S % B < B := Nat.mod_lt _ hB0
  have hSd : S = B * (S / B) + S % B := (Nat.div_add_mod S B).symm
  unfold div2by1
  simp only []
  rw [hq1, hq0, Nat.mod_eq_of_lt hq1B]
  -- Int facts for the case analysis
  have E : (d : Int) * (B * (S / B : Nat) + (S % B : Nat) - B * q) =
      B * r - (1 + e) * u1 - (B - d) * u0 := by
    have hV' : (V : Int) * d + e + 1 = B * B := by exact_mod_cast hVe
    have hS' : (S : Int) = V * u1 + u0 := by exact_mod_cast hS
    have hT' : (u1 : Int) * B + u0 = q * d + r := by
      have : (u1 : Int) * B + u0 = d * q + r := by exact_mod_cast hT
      grind
    have hSd' : (B : Int) * (S / B : Nat) + (S % B : Nat) = S := by exact_mod_cast hSd.symm
    rw [hSd']
    have := e1 B d V e u0 u1 q r S hV' hS' hT'
    exact this
  have cases := mg_cases B d e u0 u1 q r (S / B : Nat) (S % B : Nat) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) E
  generalize hQ1 : S / B = Q1 at *
  generalize hQ0 : S % B = Q0 at *
  have hu0T : (u1 * B + u0) % B = u0 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu0]
  have hrm : ∀ X, X < B → (X + (Q1 + 1) * d) % B = u0 →
      (u0 + B - (Q1 + 1) % B * d % B) % B = X := by
    intro X hX h
    apply sub_mod_eq B _ d u0 X hu0 hX
    rw [Nat.add_comm, cong_mul, Nat.add_comm]; exact h
  rcases cases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · have h1' : Q1 = q := by omega
    subst h1'
    have hX : (B - d + r + (Q1 + 1) * d) % B = u0 := by
      have : B - d + r + (Q1 + 1) * d = (u1 * B + u0) + B := by
        have : (Q1 + 1) * d = d * Q1 + d := by grind
        omega
      rw [this, Nat.add_mod_right, hu0T]
    rw [hrm _ (by omega) hX]
    have hfire : Q0 < B - d + r := by omega
    simp only [hfire, if_true]
    have e1 : ((Q1 + 1) % B + B - 1) % B = Q1 := by
      by_cases hc : Q1 + 1 < B
      · rw [Nat.mod_eq_of_lt hc]; rw [show Q1 + 1 + B - 1 = Q1 + B by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      · rw [show Q1 + 1 = B by omega, Nat.mod_self]; rw [show 0 + B - 1 = B - 1 by omega, Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (B - d + r + d) % B = r := by
      rw [show B - d + r + d = r + B by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, e2]
    simp only [show ¬ d ≤ r from by omega, if_false]
  · have h1' : q = Q1 + 1 := by omega
    have hcm : (Q1 + 1) % B = Q1 + 1 := Nat.mod_eq_of_lt (by omega)
    have hX : (r + (Q1 + 1) * d) % B = u0 := by
      have : r + (Q1 + 1) * d = (u1 * B + u0) := by
        rw [hT, h1']; grind
      rw [this, hu0T]
    rw [hrm _ (by omega) hX]
    rcases h2 with h2 | ⟨h2, h3⟩
    · have : ¬ Q0 < r := by omega
      simp only [this, if_false, show ¬ d ≤ r from by omega]
      rw [hcm]; simp only [Prod.mk.injEq]; refine ⟨?_, ?_⟩ <;> first | omega | trivial
    · have h2n : Q0 < r := by omega
      have h3n : r + d < B := by omega
      simp only [h2n, if_true]
      have e1 : (Q1 + 1 + B - 1) % B = Q1 := by
        rw [show Q1 + 1 + B - 1 = Q1 + B by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have e2 : (r + d) % B = r + d := Nat.mod_eq_of_lt h3n
      rw [hcm, e1, e2]
      simp only [show d ≤ r + d from by omega, if_true]
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [Prod.mk.injEq]; refine ⟨?_, ?_⟩ <;> first | omega | trivial
  · have h1' : q = Q1 + 2 := by omega
    have hcm : (Q1 + 1) % B = Q1 + 1 := Nat.mod_eq_of_lt (by omega)
    have hX : (r + d + (Q1 + 1) * d) % B = u0 := by
      have : r + d + (Q1 + 1) * d = (u1 * B + u0) := by
        rw [hT, h1']; grind
      rw [this, hu0T]
    rw [hrm _ (by omega) hX]
    have : ¬ Q0 < r + d := by omega
    simp only [this, if_false, show d ≤ r + d from by omega, if_true]
    rw [hcm, Nat.mod_eq_of_lt (by omega)]
    simp only [Prod.mk.injEq]; refine ⟨?_, ?_⟩ <;> first | omega | trivial

end Fv256.B

namespace Fv256.B

theorem recip_lt (d v : Nat) (hd1 : 2 ^ 63 ≤ d) (hv : v + 2 ^ 64 = (2 ^ 64 * 2 ^ 64 - 1) / d) : v < 2 ^ 64 := by
  have h1 : (2 ^ 64 * 2 ^ 64 - 1) / d ≤ (2 ^ 64 * 2 ^ 64 - 1) / 2 ^ 63 := Nat.div_le_div_left hd1 (by decide)
  have h2 : (2 ^ 64 * 2 ^ 64 - 1) / 2 ^ 63 = 2 ^ 65 - 1 := by decide
  have : v + 2 ^ 64 ≤ 2 ^ 65 - 1 := by omega
  omega

theorem mulmod_congr (a b d B : Nat) (h : a % B = b % B) : (a * d) % B = (b * d) % B := by
  rw [Nat.mul_mod a d B, Nat.mul_mod b d B, h]

theorem wv_succ (m : Janus.Arm64.Memory) (p n : Nat) :
    wv m p (n + 1) = m.readLE p 8 + 2 ^ 64 * wv m (p + 8) n := rfl

theorem wv_writeLE_outside (m : Janus.Arm64.Memory) (a len val p n : Nat) (h : a + len ≤ p ∨ p + 8 * n ≤ a) :
    wv (m.writeLE a len val) p n = wv m p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [wv]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint m val (by omega), ih (p + 8) (by omega)]

end Fv256.B

namespace Fv256.B

def Rmach (v rem U d : Nat) : Nat :=
  let B := 18446744073709551616
  let P := v * rem
  let c := (decide (B ≤ P % B + U)).toNat
  let X := rem + P / B % B + c + 1
  let Y := (X % B * d) % B
  let R1 := if (P % B + U) % B < (B - Y + U) % B then (d + (B - Y + U % B) % B) % B else (B - Y + U % B) % B
  if d < R1 ∨ (B - R1 + d) % B = 0 then (B - d + R1) % B else R1

set_option maxHeartbeats 8000000 in
theorem Rmach_eq (d V v rem U : Nat) (hBd : 2 ^ 63 ≤ d) (hdB : d < 2 ^ 64)
    (hV : V = (2 ^ 64 * 2 ^ 64 - 1) / d) (hv : V = v + 2 ^ 64) (hrem : rem < d) (hU : U < 2 ^ 64) :
    Rmach v rem U d = (div2by1 (2 ^ 64) d v rem U).2 := by
  have hvB := recip_lt d v hBd (by omega)
  have hPB : v * rem < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hvB (by omega)
  have hPB2 : v * rem / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
  unfold Rmach div2by1
  simp only [Nat.reducePow]
  generalize v * rem = P at *
  have hPm : P / 2 ^ 64 % 2 ^ 64 = P / 2 ^ 64 := Nat.mod_eq_of_lt hPB2
  simp only [Nat.reducePow] at hPm hPB2 hU hdB hBd
  rcases Nat.lt_or_ge (P % 18446744073709551616 + U) 18446744073709551616 with hc | hc
  · have hc' : ¬ 18446744073709551616 ≤ P % 18446744073709551616 + U := by omega
    simp only [hc', decide_false, Bool.toNat_false, hPm, Nat.reducePow]
    have hX : (rem + P / 18446744073709551616 + 0 + 1) % 18446744073709551616 =
        ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + U) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
      have : (P % 18446744073709551616 + U) / 18446744073709551616 = 0 := by omega
      omega
    rw [hX]
    repeat' split
    all_goals omega
  · simp only [hc, decide_true, Bool.toNat_true, hPm, Nat.reducePow]
    have hX : (rem + P / 18446744073709551616 + 1 + 1) % 18446744073709551616 =
        ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + U) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
      have : (P % 18446744073709551616 + U) / 18446744073709551616 = 1 := by omega
      omega
    rw [hX]
    repeat' split
    all_goals omega

def Qmach (v rem U d : Nat) : Nat :=
  let B := 18446744073709551616
  let P := v * rem
  let c := (decide (B ≤ P % B + U)).toNat
  let X := rem + P / B % B + c + 1
  let Y := (X % B * d) % B
  let R1 := if (P % B + U) % B < (B - Y + U) % B then (d + (B - Y + U % B) % B) % B else (B - Y + U % B) % B
  (if d < R1 ∨ (B - R1 + d) % B = 0 then 1 else 0) % 4294967296 +
    (if (P % B + U) % B < (B - Y + U) % B then (rem + P / B % B + c) % B else (rem + P / B % B + c + 1) % B)

set_option maxHeartbeats 8000000 in
theorem Qmach_eq (d V v rem U : Nat) (hBd : 2 ^ 63 ≤ d) (hdB : d < 2 ^ 64)
    (hV : V = (2 ^ 64 * 2 ^ 64 - 1) / d) (hv : V = v + 2 ^ 64) (hrem : rem < d) (hU : U < 2 ^ 64) :
    Qmach v rem U d % 2 ^ 64 = (div2by1 (2 ^ 64) d v rem U).1 := by
  have hvB := recip_lt d v hBd (by omega)
  have hPB : v * rem < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hvB (by omega)
  have hPB2 : v * rem / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
  unfold Qmach div2by1
  simp only [Nat.reducePow]
  generalize v * rem = P at *
  have hPm : P / 2 ^ 64 % 2 ^ 64 = P / 2 ^ 64 := Nat.mod_eq_of_lt hPB2
  simp only [Nat.reducePow] at hPm hPB2 hU hdB hBd
  rcases Nat.lt_or_ge (P % 18446744073709551616 + U) 18446744073709551616 with hc | hc
  · have hc' : ¬ 18446744073709551616 ≤ P % 18446744073709551616 + U := by omega
    simp only [hc', decide_false, Bool.toNat_false, hPm, Nat.reducePow]
    have hX : (rem + P / 18446744073709551616 + 0 + 1) % 18446744073709551616 =
        ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + U) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
      have : (P % 18446744073709551616 + U) / 18446744073709551616 = 0 := by omega
      omega
    rw [hX]
    repeat' split
    all_goals omega
  · simp only [hc, decide_true, Bool.toNat_true, hPm, Nat.reducePow]
    have hX : (rem + P / 18446744073709551616 + 1 + 1) % 18446744073709551616 =
        ((P / 18446744073709551616 + rem + (P % 18446744073709551616 + U) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
      have : (P % 18446744073709551616 + U) / 18446744073709551616 = 1 := by omega
      omega
    rw [hX]
    repeat' split
    all_goals omega

end Fv256.B

namespace Fv256.B

theorem byte_mod64 (j : Nat) (hj : j < 8) (x : Nat) : x / 256 ^ j % 256 = x % 2 ^ 64 / 256 ^ j % 256 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  all_goals (simp only [Nat.reducePow]; omega)

theorem writeLE_val_congr (m : Janus.Arm64.Memory) (a x y : Nat) (h : x % 2 ^ 64 = y % 2 ^ 64) :
    m.writeLE a 8 x = m.writeLE a 8 y := by
  cases m with
  | mk bytes regions =>
  simp only [Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.mk.injEq, and_true]
  funext b
  by_cases hb : a ≤ b ∧ b < a + 8
  · simp only [hb, and_self, if_true]
    have e1 : x / 256 ^ (b - a) % 256 = y / 256 ^ (b - a) % 256 := by
      rw [byte_mod64 (b - a) (by omega) x, byte_mod64 (b - a) (by omega) y, h]
    have e2 : BitVec.ofNat 8 (x / 256 ^ (b - a)) = BitVec.ofNat 8 (y / 256 ^ (b - a)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      simpa using e1
    exact e2
  · simp [hb]

theorem reachesRet_mem_congr {p : Janus.Amd64.Program} {ret : Janus.Amd64.W64} {Q : Janus.Amd64.State → Prop}
    (S : Janus.Amd64.State) (M2 : Janus.Arm64.Memory)
    (h : Janus.Amd64.Tactic.ReachesRet p ret { S with mem := M2 } Q) (hm : S.mem = M2) :
    Janus.Amd64.Tactic.ReachesRet p ret S Q := by
  cases S; simp only at hm; subst hm; exact h

end Fv256.B

namespace Fv256.B

set_option hygiene false in
/-- Closes `E = (div2by1 (2^64) d v rem uk).{1,2}` goals where `E` is the normal form of the machine's
Möller-Granlund step (see `Rmach_eq`): case split on the carry, identify the two spellings of the
estimate, split the conditionals and let `omega` finish. -/
macro "div2_close " v:ident rem:ident uk:ident d:ident hvB:ident hukB:ident hd1:ident hd2:ident hrem:ident : tactic =>
  `(tactic| (
    unfold Fv256.B.div2by1
    have hPB : $v * $rem < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' $hvB (by omega)
    have hPB2 : $v * $rem / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul hPB
    simp only [Nat.reducePow]
    generalize $v * $rem = P at *
    have hPm : P / 2 ^ 64 % 2 ^ 64 = P / 2 ^ 64 := Nat.mod_eq_of_lt hPB2
    simp only [Nat.reducePow] at hPm hPB2 $hukB $hd2 $hd1
    rcases Nat.lt_or_ge (P % 18446744073709551616 + $uk) 18446744073709551616 with hc | hc
    · have hc' : ¬ 18446744073709551616 ≤ P % 18446744073709551616 + $uk := by omega
      simp only [hc', decide_false, Bool.toNat_false, hPm, Nat.reducePow]
      have hX : ($rem + P / 18446744073709551616 + 0 + 1) % 18446744073709551616 =
          ((P / 18446744073709551616 + $rem + (P % 18446744073709551616 + $uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
        have : (P % 18446744073709551616 + $uk) / 18446744073709551616 = 0 := by omega
        omega
      rw [hX]
      repeat' split
      all_goals omega
    · simp only [hc, decide_true, Bool.toNat_true, hPm, Nat.reducePow]
      have hX : ($rem + P / 18446744073709551616 + 1 + 1) % 18446744073709551616 =
          ((P / 18446744073709551616 + $rem + (P % 18446744073709551616 + $uk) / 18446744073709551616) % 18446744073709551616 + 1) % 18446744073709551616 := by
        have : (P % 18446744073709551616 + $uk) / 18446744073709551616 = 1 := by omega
        omega
      rw [hX]
      repeat' split
      all_goals omega))

end Fv256.B

namespace Fv256.B

/-- Knuth's quotient-digit estimate with the single `qhat*dl > rhat*B + u0` correction used by `udivremKnuth`. -/
def qhat1 (B dh dl u2 u1 u0 : Nat) : Nat :=
  if dh ≤ u2 then B - 1
  else if (((u2 * B + u1) / dh) * dl > ((u2 * B + u1) % dh) * B + u0) then (u2 * B + u1) / dh - 1
  else (u2 * B + u1) / dh

theorem qhat1_bounds (B dh dl u2 u1 u0 β D X : Nat)
    (hdh2 : B ≤ 2 * dh) (hdhB : dh < B) (hdl : dl < B) (hu0 : u0 < B) (hu1 : u1 < B) (hu2 : u2 < B)
    (hβ : 0 < β)
    (hD1 : (dh * B + dl) * β ≤ D) (hD2 : D < (dh * B + dl + 1) * β)
    (hX1 : ((u2 * B + u1) * B + u0) * β ≤ X) (hX2 : X < (((u2 * B + u1) * B + u0) + 1) * β)
    (hXD : X < B * D) :
    X / D ≤ qhat1 B dh dl u2 u1 u0 ∧ qhat1 B dh dl u2 u1 u0 ≤ X / D + 1 := by
  have hD2pos : 0 < dh * B + dl := by
    have : 0 < dh := by omega
    have : 0 < B := by omega
    have := Nat.mul_pos ‹0 < dh› ‹0 < B›
    omega
  have hD0 : 0 < D := Nat.lt_of_lt_of_le (Nat.mul_pos hD2pos hβ) hD1
  have hdiv := Nat.div_add_mod X D
  have hmod := Nat.mod_lt X hD0
  obtain ⟨q, hq⟩ : ∃ q, q = X / D := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = X % D := ⟨_, rfl⟩
  rw [← hq, ← hr] at hdiv
  rw [← hr] at hmod
  rw [← hq]
  have hqB : q < B := by
    refine Nat.lt_of_mul_lt_mul_right (a := D) ?_
    have : q * D ≤ X := by rw [Nat.mul_comm q D]; omega
    omega
  have hqD : q * D ≤ X := by rw [Nat.mul_comm q D]; omega
  have hXq : X < (q + 1) * D := by rw [Nat.succ_mul, Nat.mul_comm q D]; omega
  unfold qhat1
  by_cases hA : dh ≤ u2
  · simp only [hA, ite_true]
    refine ⟨by omega, ?_⟩
    refine Nat.le_of_not_lt (fun hlt => ?_)
    -- q + 3 ≤ B
    have h1 : (q + 1) * D ≤ (B - 2) * D := Nat.mul_le_mul_right _ (by omega)
    have h2 : (B - 2) * D ≤ (B - 2) * ((dh * B + dl + 1) * β) := Nat.mul_le_mul_left _ (Nat.le_of_lt hD2)
    have h3 : dh * B ≤ u2 * B + u1 := by
      have := Nat.mul_le_mul_right B hA
      omega
    have h4 : dh * B * B * β ≤ ((u2 * B + u1) * B + u0) * β := Nat.mul_le_mul_right _ (by
      have := Nat.mul_le_mul_right B h3
      omega)
    have h5 : (dh * B + dl + 1) ≤ (dh + 1) * B := by
      have : (dh + 1) * B = dh * B + B := by grind
      omega
    have h6 : (B - 2) * ((dh * B + dl + 1) * β) ≤ (B - 2) * (((dh + 1) * B) * β) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h5)
    have h7 : dh * B * B * β < (B - 2) * (((dh + 1) * B) * β) := by omega
    have h8 : dh * B < (B - 2) * (dh + 1) := by
      have e1 : dh * B * B * β = (dh * B) * (B * β) := by grind
      have e2 : (B - 2) * (((dh + 1) * B) * β) = ((B - 2) * (dh + 1)) * (B * β) := by grind
      rw [e1, e2] at h7
      exact Nat.lt_of_mul_lt_mul_right h7
    have h9 : (B - 2) * (dh + 1) + 2 * (dh + 1) = B * (dh + 1) := by
      rw [← Nat.add_mul]; congr 1; omega
    have h10 : B * (dh + 1) = dh * B + B := by grind
    omega
  · simp only [hA, if_false]
    have hu2 : u2 < dh := by omega
    obtain ⟨qh, hqh⟩ : ∃ qh, qh = (u2 * B + u1) / dh := ⟨_, rfl⟩
    obtain ⟨rh, hrh⟩ : ∃ rh, rh = (u2 * B + u1) % dh := ⟨_, rfl⟩
    have hN2 := Nat.div_add_mod (u2 * B + u1) dh
    rw [← hqh, ← hrh] at hN2
    have hrhd : rh < dh := by rw [hrh]; exact Nat.mod_lt _ (by omega)
    rw [← hqh, ← hrh]
    obtain ⟨N2, hN2d⟩ : ∃ N2, N2 = u2 * B + u1 := ⟨_, rfl⟩
    rw [← hN2d] at hN2 hX1 hX2
    obtain ⟨N3, hN3d⟩ : ∃ N3, N3 = N2 * B + u0 := ⟨_, rfl⟩
    rw [← hN3d] at hX1 hX2
    obtain ⟨D2, hD2d⟩ : ∃ D2, D2 = dh * B + dl := ⟨_, rfl⟩
    rw [← hD2d] at hD1 hD2 hD2pos
    have hi : q * D2 ≤ N3 := by
      have h1 : q * D2 * β ≤ q * D := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hD1
      have h2 : q * D2 * β < (N3 + 1) * β := by omega
      have := Nat.lt_of_mul_lt_mul_right h2
      omega
    have hiv : N3 < (q + 1) * (D2 + 1) := by
      have h1 : (q + 1) * D ≤ (q + 1) * ((D2 + 1) * β) := Nat.mul_le_mul_left _ (Nat.le_of_lt hD2)
      have h2 : N3 * β < ((q + 1) * (D2 + 1)) * β := by
        have e : (q + 1) * ((D2 + 1) * β) = ((q + 1) * (D2 + 1)) * β := by grind
        omega
      exact Nat.lt_of_mul_lt_mul_right h2
    have hD2gt : q < D2 := by
      have : dh * B ≤ D2 := by omega
      have : B * 1 ≤ dh * B := by
        have := Nat.mul_le_mul_right B (show 1 ≤ dh by omega)
        omega
      omega
    have hii : N3 < (qh + 1) * D2 := by
      have h1 : N3 < (N2 + 1) * B := by rw [hN3d, Nat.add_mul]; omega
      have h2 : (N2 + 1) * B ≤ (dh * qh + dh) * B := Nat.mul_le_mul_right _ (by omega)
      have h3 : (dh * qh + dh) * B = dh * B * (qh + 1) := by grind
      have h4 : dh * B * (qh + 1) ≤ D2 * (qh + 1) := Nat.mul_le_mul_right _ (by omega)
      have h5 : D2 * (qh + 1) = (qh + 1) * D2 := by grind
      omega
    have hv : qh ≤ q + 2 := by
      refine Nat.le_of_not_lt (fun hlt => ?_)
      have h1 : dh * (q + 3) ≤ dh * qh := Nat.mul_le_mul_left _ (by omega)
      have h2 : dh * B * (q + 3) ≤ N3 := by
        have : dh * (q + 3) ≤ N2 := by omega
        have := Nat.mul_le_mul_right B this
        have e : dh * B * (q + 3) = dh * (q + 3) * B := by grind
        omega
      have h3 : (q + 1) * (D2 + 1) ≤ (q + 1) * ((dh + 1) * B) := Nat.mul_le_mul_left _ (by
        have : (dh + 1) * B = dh * B + B := by grind
        omega)
      have h4 : dh * B * (q + 3) < (q + 1) * (dh + 1) * B := by
        have e : (q + 1) * ((dh + 1) * B) = (q + 1) * (dh + 1) * B := by grind
        omega
      have h5 : dh * (q + 3) < (q + 1) * (dh + 1) := by
        have e1 : dh * B * (q + 3) = dh * (q + 3) * B := by grind
        rw [e1] at h4
        exact Nat.lt_of_mul_lt_mul_right h4
      have h6 : (q + 1) * (dh + 1) = (q + 1) * dh + (q + 1) := by grind
      have h7 : dh * (q + 3) = dh * q + 3 * dh := by grind
      have h8 : (q + 1) * dh = q * dh + dh := by grind
      have h9 : dh * q = q * dh := by grind
      omega
    have hT : (qh * dl > rh * B + u0) ↔ N3 < qh * D2 := by
      have e1 : qh * D2 = qh * dh * B + qh * dl := by rw [hD2d]; grind
      have e2 : N3 = N2 * B + u0 := hN3d
      have e3 : N2 * B = (dh * qh + rh) * B := by rw [hN2]
      have e4 : (dh * qh + rh) * B = dh * qh * B + rh * B := by grind
      have e5 : dh * qh * B = qh * dh * B := by grind
      constructor <;> intro h <;> omega
    by_cases hTc : qh * dl > rh * B + u0
    · simp only [hTc, ite_true]
      have := hT.mp hTc
      refine ⟨?_, ?_⟩
      · have : q < qh := by
          refine Nat.lt_of_not_ge (fun hge => ?_)
          have := Nat.mul_le_mul_right D2 hge
          omega
        omega
      · omega
    · simp only [hTc, if_false]
      have hn : ¬ N3 < qh * D2 := fun h => hTc (hT.mpr h)
      refine ⟨?_, ?_⟩
      · refine Nat.le_of_not_lt (fun hlt => ?_)
        have := Nat.mul_le_mul_right D2 (show qh + 1 ≤ q by omega)
        omega
      · refine Nat.le_of_not_lt (fun hlt => ?_)
        have : (q + 2) * D2 ≤ qh * D2 := Nat.mul_le_mul_right D2 (by omega)
        have e : (q + 2) * D2 = (q + 1) * D2 + D2 := by grind
        have e2 : (q + 1) * (D2 + 1) = (q + 1) * D2 + q + 1 := by grind
        omega

end Fv256.B

namespace Fv256.B

theorem knuth_nb (P D u2 Z qh q r b : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P)
    (hq1 : q * D ≤ u2 * P + Z) (hq2 : u2 * P + Z < (q + 1) * D)
    (hqh : q ≤ qh ∧ qh ≤ q + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) (hb : b ≤ u2) :
    qh = q ∧ b = u2 ∧ r = u2 * P + Z - q * D := by
  have e1 : (q + 1) * D = q * D + D := by grind
  obtain ⟨t, ht⟩ : ∃ t, u2 = b + t := ⟨u2 - b, by omega⟩
  have e2 : u2 * P = b * P + t * P := by rw [ht, Nat.add_mul]
  have hP : 0 < P := by omega
  rcases (show qh = q ∨ qh = q + 1 by omega) with h | h
  · subst h
    have : t = 0 := by
      refine Nat.eq_zero_of_not_pos (fun htp => ?_)
      have : P ≤ t * P := Nat.le_mul_of_pos_left P htp
      omega
    subst this
    refine ⟨rfl, by omega, by omega⟩
  · exfalso
    subst h
    have e3 : (q + 1) * D = q * D + D := e1
    have : 0 ≤ t * P := Nat.zero_le _
    omega

/-- Borrow case: the estimate was one too large; adding `D` back (dropping the carry out) repairs it. -/
theorem knuth_borrow (P D u2 Z qh q r b : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P)
    (hq1 : q * D ≤ u2 * P + Z) (hq2 : u2 * P + Z < (q + 1) * D)
    (hqh : q ≤ qh ∧ qh ≤ q + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) (hb : u2 < b) :
    qh = q + 1 ∧ b = u2 + 1 ∧ P ≤ r + D ∧ r + D - P = u2 * P + Z - q * D := by
  have e1 : (q + 1) * D = q * D + D := by grind
  obtain ⟨t, ht⟩ : ∃ t, b = u2 + 1 + t := ⟨b - u2 - 1, by omega⟩
  have e2 : b * P = u2 * P + P + t * P := by
    rw [ht, Nat.add_mul, Nat.add_mul, Nat.one_mul]
  have hP : 0 < P := by omega
  rcases (show qh = q ∨ qh = q + 1 by omega) with h | h
  · exfalso
    subst h
    have : 0 ≤ t * P := Nat.zero_le _
    omega
  · subst h
    have : t = 0 := by
      refine Nat.eq_zero_of_not_pos (fun htp => ?_)
      have : P ≤ t * P := Nat.le_mul_of_pos_left P htp
      omega
    subst this
    refine ⟨rfl, by omega, by omega, by omega⟩

end Fv256.B

namespace Fv256.B

/-- The correction loop of `bits.Div64` for one half digit (base `b = 2^32`): decrement the estimate while it is
`≥ b` or too large for the next digit, stopping when the remainder estimate reaches `b`. -/
def hloop (b yn1 yn0 un1 : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | qh + 1, rh =>
    if (qh + 1 ≥ b ∨ (qh + 1) * yn0 > b * rh + un1) then
      (if rh + yn1 ≥ b then qh else hloop b yn1 yn0 un1 qh (rh + yn1))
    else qh + 1

theorem hloop_correct (b yn1 yn0 un32 un1 : Nat) (hb : 0 < b) (hy2 : b ≤ 2 * yn1) (hy1 : yn1 < b) (hy0 : yn0 < b)
    (hun1 : un1 < b) (hlt : un32 < yn1 * b + yn0) :
    ∀ qh rh, qh * yn1 + rh = un32 → (un32 * b + un1) / (yn1 * b + yn0) ≤ qh → qh ≤ b + 1 →
      hloop b yn1 yn0 un1 qh rh = (un32 * b + un1) / (yn1 * b + yn0) := by
  intro qh
  induction qh with
  | zero =>
    intro rh _ hq _
    simp only [hloop]
    exact (Nat.le_zero.mp hq).symm
  | succ qh ih =>
    intro rh h1 hq hqb
    have hy : 0 < yn1 * b + yn0 := by
      have : 0 < yn1 := by omega
      have := Nat.mul_pos this hb
      omega
    have hqN := Nat.div_add_mod (un32 * b + un1) (yn1 * b + yn0)
    have hmod := Nat.mod_lt (un32 * b + un1) hy
    obtain ⟨q, hqd⟩ : ∃ q, q = (un32 * b + un1) / (yn1 * b + yn0) := ⟨_, rfl⟩
    obtain ⟨r, hrd⟩ : ∃ r, r = (un32 * b + un1) % (yn1 * b + yn0) := ⟨_, rfl⟩
    rw [← hqd, ← hrd] at hqN
    rw [← hrd] at hmod
    rw [← hqd] at hq ⊢
    -- y*q ≤ N < y*(q+1)
    obtain ⟨y, hyd⟩ : ∃ y, y = yn1 * b + yn0 := ⟨_, rfl⟩
    rw [← hyd] at hqN hmod hlt hy
    have hqy : y * q ≤ un32 * b + un1 := by omega
    have hqy2 : un32 * b + un1 < y * q + y := by omega
    have hqb' : q < b := by
      refine Nat.lt_of_mul_lt_mul_left (a := y) ?_
      have : (un32 + 1) * b ≤ y * b := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul] at this
      have e : y * b = b * y := by grind
      omega
    have hA : (qh + 1) * yn1 + rh = un32 := h1
    have hP : (qh + 1) * y = (qh + 1) * yn1 * b + (qh + 1) * yn0 := by rw [hyd]; grind
    have hN : un32 * b = (qh + 1) * yn1 * b + rh * b := by rw [← hA]; grind
    simp only [hloop]
    by_cases hc : (qh + 1 ≥ b ∨ (qh + 1) * yn0 > b * rh + un1)
    · simp only [hc, if_true]
      have hqlt : q < qh + 1 := by
        rcases hc with hc | hc
        · omega
        · refine Nat.lt_of_not_ge (fun hge => ?_)
          have := Nat.mul_le_mul_left y hge
          have e : b * rh = rh * b := by grind
          have e2 : y * (qh + 1) = (qh + 1) * y := by grind
          omega
      by_cases hr : rh + yn1 ≥ b
      · simp only [hr, if_true]
        -- qh = q
        refine Nat.le_antisymm (Nat.le_of_not_lt (fun hlt' => ?_)) (by omega)
        have h2 : (qh + 1) * yn1 = qh * yn1 + yn1 := by grind
        have h3 : qh * yn0 < b * b := by
          have : qh * yn0 ≤ b * yn0 := Nat.mul_le_mul_right _ (by omega)
          have : b * yn0 < b * b := Nat.mul_lt_mul_of_pos_left hy0 hb
          omega
        have h4 : qh * y = qh * yn1 * b + qh * yn0 := by rw [hyd]; grind
        have h5 : qh * yn1 * b + (rh + yn1) * b = un32 * b := by
          have : qh * yn1 + (rh + yn1) = un32 := by omega
          rw [← this]; grind
        have h6 : b * b ≤ (rh + yn1) * b := Nat.mul_le_mul_right _ hr
        have h7 : qh * y ≤ un32 * b := by omega
        have h8 : y * (qh) ≤ un32 * b + un1 := by
          have : y * qh = qh * y := by grind
          omega
        have h9 := Nat.mul_le_mul_left y (show q + 1 ≤ qh by omega)
        have e : y * (q + 1) = y * q + y := by grind
        omega
      · simp only [hr, if_false]
        have hr' : ¬ (rh + yn1 ≥ b) := hr
        have h2 : (qh + 1) * yn1 = qh * yn1 + yn1 := by grind
        rw [ih (rh + yn1) (by omega) (by omega) (by omega), hqd]
    · simp only [hc, if_false]
      have hc1 : qh + 1 < b := by omega
      have hc2 : (qh + 1) * yn0 ≤ b * rh + un1 := by omega
      refine Nat.le_antisymm ?_ hq
      refine Nat.le_of_not_lt (fun hlt' => ?_)
      have h9 : (qh + 1) * y ≤ un32 * b + un1 := by
        have e : b * rh = rh * b := by grind
        omega
      have h10 := Nat.mul_le_mul_left y (show q + 1 ≤ qh + 1 by omega)
      have e : y * (q + 1) = y * q + y := by grind
      have e2 : y * (qh + 1) = (qh + 1) * y := by grind
      omega

end Fv256.B

namespace Fv256.B
open Fv256


theorem div_top (a c : Nat) (ha : a < 6277101735386680763835789423207666416102355444464034512896) :
    (a + 6277101735386680763835789423207666416102355444464034512896 * c) /
      6277101735386680763835789423207666416102355444464034512896 = c := by
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt ha]; simp

theorem lsh_top0 (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    ((x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ t %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) /
      6277101735386680763835789423207666416102355444464034512896 = x3 * 2 ^ t % 18446744073709551616 + x2 / 2 ^ (64 - t) := by
  rw [← Util.lsh0_t x0 x1 x2 x3 t ht h0 h1 h2 h3]
  have l1 := Util.lo_hi_lt x1 x0 t ht h0
  have l2 := Util.lo_hi_lt x2 x1 t ht h1
  have l0 : x0 * 2 ^ t % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have e : ∀ a b c d : Nat, a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
      6277101735386680763835789423207666416102355444464034512896 * d =
      (a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c) +
      6277101735386680763835789423207666416102355444464034512896 * d := fun a b c d => by omega
  rw [e]
  apply div_top
  omega

theorem lsh_top1 (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    ((x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (64 + t) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) /
      6277101735386680763835789423207666416102355444464034512896 = x2 * 2 ^ t % 18446744073709551616 + x1 / 2 ^ (64 - t) := by
  rw [← Util.lsh1_t x0 x1 x2 x3 t ht h0 h1 h2 h3]
  have l1 := Util.lo_hi_lt x1 x0 t ht h0
  have l2 := Util.lo_hi_lt x2 x1 t ht h1
  have l0 : x0 * 2 ^ t % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have e : ∀ a b c : Nat, 18446744073709551616 * a + 340282366920938463463374607431768211456 * b +
      6277101735386680763835789423207666416102355444464034512896 * c =
      (18446744073709551616 * a + 340282366920938463463374607431768211456 * b) +
      6277101735386680763835789423207666416102355444464034512896 * c := fun a b c => by omega
  rw [e]
  apply div_top
  omega

theorem lsh_top2 (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    ((x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (128 + t) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) /
      6277101735386680763835789423207666416102355444464034512896 = x1 * 2 ^ t % 18446744073709551616 + x0 / 2 ^ (64 - t) := by
  rw [← Util.lsh2_t x0 x1 x2 x3 t ht h0 h1 h2 h3]
  have l1 := Util.lo_hi_lt x1 x0 t ht h0
  have l0 : x0 * 2 ^ t % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have e : ∀ a b : Nat, 340282366920938463463374607431768211456 * a +
      6277101735386680763835789423207666416102355444464034512896 * b =
      (340282366920938463463374607431768211456 * a) +
      6277101735386680763835789423207666416102355444464034512896 * b := fun a b => rfl
  rw [e]
  apply div_top
  omega

theorem lsh_top3 (x0 x1 x2 x3 t : Nat) (ht : t < 64) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) :
    ((x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) * 2 ^ (192 + t) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936) /
      6277101735386680763835789423207666416102355444464034512896 = x0 * 2 ^ t % 18446744073709551616 := by
  rw [← Util.lsh3_t x0 x1 x2 x3 t ht h0 h1 h2 h3]
  have l0 : x0 * 2 ^ t % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have := div_top 0 (x0 * 2 ^ t % 18446744073709551616) (by decide)
  simpa using this



theorem f64_core (V n F : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ 192) (hbl : Spec.bitLen V = 257 - n)
    (hV : V < 2 ^ 256) (hF : F = (V * 2 ^ n % 2 ^ 256) / 2 ^ 192) :
    ((1279 - n) * 2 ^ 64 + F) / 2 ^ 12 % 2 ^ 64 = (1279 - n) * 2 ^ 52 + V / 2 ^ (204 - n) % 2 ^ 52 := by
  have hV0 : V ≠ 0 := by
    intro h; subst h; simp [Spec.bitLen] at hbl; omega
  have hlog : Nat.log2 V = 256 - n := by
    unfold Spec.bitLen at hbl; rw [if_neg hV0] at hbl; omega
  obtain ⟨hl1, hl2⟩ := (Nat.log2_eq_iff hV0).mp hlog
  obtain ⟨R, hR⟩ : ∃ R, V = 2 ^ (256 - n) + R := ⟨V - 2 ^ (256 - n), by omega⟩
  have hRlt : R < 2 ^ (256 - n) := by
    have : 2 ^ (256 - n + 1) = 2 * 2 ^ (256 - n) := by rw [Nat.pow_succ]; omega
    omega
  have e256 : 2 ^ 256 = 2 ^ (256 - n) * 2 ^ n := by rw [← Nat.pow_add]; congr 1; omega
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  have hP2 : 0 < 2 ^ (256 - n) := Nat.two_pow_pos _
  have hRn : R * 2 ^ n < 2 ^ 256 := by
    rw [e256]; exact Nat.mul_lt_mul_of_pos_right hRlt hP
  have hVn : V * 2 ^ n % 2 ^ 256 = R * 2 ^ n := by
    have : V * 2 ^ n = 2 ^ 256 + R * 2 ^ n := by rw [hR, Nat.add_mul, ← e256]
    rw [this, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt hRn]
  rw [hVn] at hF
  have e192 : 2 ^ 204 = 2 ^ n * 2 ^ (204 - n) := by rw [← Nat.pow_add]; congr 1; omega
  have hF12 : F / 2 ^ 12 = R / 2 ^ (204 - n) := by
    rw [hF, Nat.div_div_eq_div_mul, show 2 ^ 192 * 2 ^ 12 = 2 ^ 204 by rw [← Nat.pow_add], e192, Nat.mul_comm R,
      Nat.mul_div_mul_left _ _ hP]
  have hRq : R / 2 ^ (204 - n) < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have : 2 ^ (256 - n) = 2 ^ 52 * 2 ^ (204 - n) := by rw [← Nat.pow_add]; congr 1; omega
    omega
  have hVq : V / 2 ^ (204 - n) % 2 ^ 52 = R / 2 ^ (204 - n) := by
    have : 2 ^ (256 - n) = 2 ^ (204 - n) * 2 ^ 52 := by rw [← Nat.pow_add]; congr 1; omega
    rw [hR, this, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    rw [Nat.add_comm, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt hRq
  rw [hVq]
  have hFlt : F < 2 ^ 64 := by
    rw [hF]; apply Nat.div_lt_of_lt_mul
    have : 2 ^ 256 = 2 ^ 192 * 2 ^ 64 := by rw [← Nat.pow_add]
    omega
  have e64 : 2 ^ 64 = 2 ^ 12 * 2 ^ 52 := by rw [← Nat.pow_add]
  have h12 : ((1279 - n) * 2 ^ 64 + F) / 2 ^ 12 = (1279 - n) * 2 ^ 52 + F / 2 ^ 12 := by
    have : (1279 - n) * 2 ^ 64 = 2 ^ 12 * ((1279 - n) * 2 ^ 52) := by
      rw [e64]; grind
    rw [this, Nat.mul_add_div (Nat.two_pow_pos 12)]
  rw [h12, hF12]
  apply Nat.mod_eq_of_lt
  have : (1279 - n) * 2 ^ 52 + R / 2 ^ (204 - n) < (1279 - n + 1) * 2 ^ 52 := by
    rw [Nat.add_mul]; omega
  have h2 : (1279 - n + 1) * 2 ^ 52 ≤ 2048 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
  have : 2048 * 2 ^ 52 = 2 ^ 63 := by decide
  have : 2 ^ 63 < 2 ^ 64 := by decide
  omega

end Fv256.B

namespace Fv256.B
open Fv256


theorem f64_gen (V n F : Nat) (hn1 : 1 ≤ n) (hn2 : n ≤ 192) (hbl : Spec.bitLen V = 257 - n)
    (hV : V < 2 ^ 256) (hVge : 2 ^ 64 ≤ V) (hF : F = (V * 2 ^ n % 2 ^ 256) / 2 ^ 192) :
    ((1279 - n) * 2 ^ 64 + F) / 2 ^ 12 % 2 ^ 64 = float64Bits V := by
  have hcore := f64_core V n F hn1 hn2 hbl hV hF
  unfold float64Bits
  rw [if_neg (by omega), hbl]
  have e2 : 257 - n + 1022 = 1279 - n := by omega
  have e3 : 257 - n - 53 = 204 - n := by omega
  rw [e2, e3]
  exact hcore

/-- bit length of a 256-bit number from the position of its top nonzero limb. -/
theorem f64_bl3 (x0 x1 x2 x3 k : Nat) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (h3 : x3 < 18446744073709551616) (hx3 : x3 ≠ 0)
    (hk : Janus.Arm64.clzNat 64 x3 = k) :
    Spec.bitLen (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * x3) = 256 - k := by
  have := Util.clz_bl 64 x3 h3
  have h := Util.bl_4 x0 x1 x2 x3 h0 h1 h2
  rw [if_pos hx3] at h
  omega

theorem f64_bl2 (x0 x1 x2 k : Nat) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616)
    (h2 : x2 < 18446744073709551616) (hx2 : x2 ≠ 0)
    (hk : Janus.Arm64.clzNat 64 x2 = k) :
    Spec.bitLen (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * x2 +
        6277101735386680763835789423207666416102355444464034512896 * 0) = 192 - k := by
  have := Util.clz_bl 64 x2 h2
  have h := Util.bl_4 x0 x1 x2 0 h0 h1 h2
  simp only [ne_eq, not_true_eq_false, if_false, hx2, not_false_eq_true, if_true] at h
  omega

theorem f64_bl1 (x0 x1 k : Nat) (h0 : x0 < 18446744073709551616) (h1 : x1 < 18446744073709551616) (hx1 : x1 ≠ 0)
    (hk : Janus.Arm64.clzNat 64 x1 = k) :
    Spec.bitLen (x0 + 18446744073709551616 * x1 + 340282366920938463463374607431768211456 * 0 +
        6277101735386680763835789423207666416102355444464034512896 * 0) = 128 - k := by
  have := Util.clz_bl 64 x1 h1
  have h := Util.bl_4 x0 x1 0 0 h0 h1 (by decide)
  simp only [ne_eq, not_true_eq_false, if_false, hx1, not_false_eq_true, if_true] at h
  omega


end Fv256.B

namespace Fv256.B

theorem or3_zero_iff (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b ||| BitVec.ofNat 64 c).toNat = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.or_eq_zero_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hc, and_assoc]

theorem or2_zero_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b).toNat = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.or_eq_zero_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]


end Fv256.B

namespace Fv256.B
open Fv256

theorem f64_asm_eq (F e : Nat) (hF : F < 2 ^ 64) (he : e < 2 ^ 11) :
    (e * 2 ^ 64 + F) / 2 ^ 12 % 2 ^ 64 = e * 2 ^ 52 + F / 2 ^ 12 := by
  have e64 : 2 ^ 64 = 2 ^ 12 * 2 ^ 52 := by rw [← Nat.pow_add]
  have h12 : (e * 2 ^ 64 + F) / 2 ^ 12 = e * 2 ^ 52 + F / 2 ^ 12 := by
    have : e * 2 ^ 64 = 2 ^ 12 * (e * 2 ^ 52) := by rw [e64]; grind
    rw [this, Nat.mul_add_div (Nat.two_pow_pos 12)]
  rw [h12]
  apply Nat.mod_eq_of_lt
  have h1 : F / 2 ^ 12 < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have h2 : (e + 1) * 2 ^ 52 ≤ 2 ^ 11 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
  have h3 : 2 ^ 11 * 2 ^ 52 = 2 ^ 63 := by rw [← Nat.pow_add]
  have h4 : 2 ^ 63 < 2 ^ 64 := by decide
  rw [Nat.add_mul] at h2
  omega

theorem assemble_toNat (F e : Nat) (hF : F < 2 ^ 64) (he : e + 1022 < 2 ^ 11) :
    (BitVec.ofNat 64 F >>> 12 ||| (BitVec.ofNat 64 e + 1022#64) <<< 52).toNat = (e + 1022) * 2 ^ 52 + F / 2 ^ 12 := by
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hF]
  have h1 : F / 2 ^ 12 < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hm : (e % 2 ^ 64 + 1022) % 2 ^ 64 = e + 1022 := by
    have : e < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]; exact Nat.mod_eq_of_lt (by omega)
  rw [hm]
  have h2 : (e + 1022) * 2 ^ 52 < 2 ^ 64 := by
    have : (e + 1022) * 2 ^ 52 ≤ 2 ^ 11 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
    exact Nat.lt_of_le_of_lt this (by decide)
  rw [Nat.mod_eq_of_lt h2, Util.or_hi _ _ 52 h1, Nat.add_comm]

theorem funnel (a b t : Nat) (ht : t < 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((a * 2 ^ 64 + b) * 2 ^ t / 2 ^ 64) % 2 ^ 64 = a * 2 ^ t % 2 ^ 64 + b / 2 ^ (64 - t) := by
  have e64 : 2 ^ 64 = 2 ^ t * 2 ^ (64 - t) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : (a * 2 ^ 64 + b) * 2 ^ t = 2 ^ 64 * (a * 2 ^ t) + b * 2 ^ t := by grind
  have h2 : b * 2 ^ t / 2 ^ 64 = b / 2 ^ (64 - t) := by
    rw [e64, Nat.mul_comm b, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos t)]
  rw [h1, Nat.mul_add_div (Nat.two_pow_pos 64), h2]
  have hlt := Util.lo_hi_lt a b t ht hb
  simp only [Nat.reducePow] at hlt ⊢
  have hc : b / 2 ^ (64 - t) < 18446744073709551616 := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hlt]


end Fv256.B

namespace Fv256.B
open Fv256

theorem assemble_bv (G : BitVec 64) (e : Nat) (he : e + 1022 < 2 ^ 11) :
    (G >>> 12 ||| (BitVec.ofNat 64 e + 1022#64) <<< 52).toNat = (e + 1022) * 2 ^ 52 + G.toNat / 2 ^ 12 := by
  have hF : G.toNat < 2 ^ 64 := G.isLt
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h1 : G.toNat / 2 ^ 12 < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
  have hm : (e % 2 ^ 64 + 1022) % 2 ^ 64 = e + 1022 := by
    have : e < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt this]; exact Nat.mod_eq_of_lt (by omega)
  rw [hm]
  have h2 : (e + 1022) * 2 ^ 52 < 2 ^ 64 := by
    have : (e + 1022) * 2 ^ 52 ≤ 2 ^ 11 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
    exact Nat.lt_of_le_of_lt this (by decide)
  rw [Nat.mod_eq_of_lt h2, Util.or_hi _ _ 52 h1, Nat.add_comm]

theorem mask_and (y : BitVec 64) : (18446744073709551615#64 &&& y) = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and]
  have := y.isLt
  show 18446744073709551615 &&& y.toNat = y.toNat
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 by decide, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]

theorem shld_toNat (a b t : Nat) (ht1 : 1 ≤ t) (ht : t < 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a >>> (64 - t)) ||| (BitVec.ofNat 64 b <<< t)).toNat = b * 2 ^ t % 2 ^ 64 + a / 2 ^ (64 - t) := by
  have h := Util.shl_or b a t ht hb ha
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.or_comm]
  simp only [Nat.reducePow] at h ⊢
  have hor : (b * 2 ^ t % 18446744073709551616 ||| a / 2 ^ (64 - t)) < 18446744073709551616 :=
    Nat.or_lt_two_pow (n := 64) (Nat.mod_lt _ (by decide)) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)
  rw [Nat.mod_eq_of_lt hor] at h
  exact h


end Fv256.B

namespace Fv256.B

theorem and_mask (y : BitVec 64) : (y &&& 18446744073709551615#64) = y := by
  rw [BitVec.and_comm]; exact mask_and y

end Fv256.B
