import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB

namespace Fv256.B

theorem wv_top2 (m : Janus.Arm64.Memory) (p N : Nat) (h : 2 ≤ N) :
    ∃ lo, lo < 2 ^ (64 * (N - 2)) ∧
      wv m p N = lo + 2 ^ (64 * (N - 2)) * (m.readLE (p + 8 * (N - 2)) 8 + 2 ^ 64 * m.readLE (p + 8 * (N - 1)) 8) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 2 := ⟨N - 2, by omega⟩
  refine ⟨wv m p K, wv_lt m p K, ?_⟩
  have e1 : K + 2 - 2 = K := by omega
  have e2 : K + 2 - 1 = K + 1 := by omega
  rw [e1, e2, wv_snoc m p (K + 1), wv_snoc m p K]
  have e3 : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by
    rw [Nat.mul_succ, Nat.pow_add]
  rw [e3]
  grind

theorem wv_top3 (m : Janus.Arm64.Memory) (p N : Nat) (h : 3 ≤ N) :
    ∃ lo, lo < 2 ^ (64 * (N - 3)) ∧
      wv m p N = lo + 2 ^ (64 * (N - 3)) * (m.readLE (p + 8 * (N - 3)) 8 + 2 ^ 64 * (m.readLE (p + 8 * (N - 2)) 8 +
        2 ^ 64 * m.readLE (p + 8 * (N - 1)) 8)) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 3 := ⟨N - 3, by omega⟩
  refine ⟨wv m p K, wv_lt m p K, ?_⟩
  have e1 : K + 3 - 3 = K := by omega
  have e2 : K + 3 - 2 = K + 1 := by omega
  have e2' : K + 3 - 1 = K + 2 := by omega
  rw [e1, e2, e2', wv_snoc m p (K + 2), wv_snoc m p (K + 1), wv_snoc m p K]
  have e3 : 2 ^ (64 * (K + 1)) = 2 ^ (64 * K) * 2 ^ 64 := by
    rw [Nat.mul_succ, Nat.pow_add]
  have e4 : 2 ^ (64 * (K + 2)) = 2 ^ (64 * K) * 2 ^ 64 * 2 ^ 64 := by
    rw [show 64 * (K + 2) = 64 * K + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
  rw [e3, e4]
  grind

theorem est_ok (M Md : Janus.Arm64.Memory) (p dp n : Nat) (hn : 2 ≤ n) (D X dh dl u2 u1 u0 : Nat)
    (hD : D = wv Md dp n) (hX : X = wv M p (n + 1))
    (hdh : dh = Md.readLE (dp + 8 * (n - 1)) 8) (hdl : dl = Md.readLE (dp + 8 * (n - 2)) 8)
    (hu2 : u2 = M.readLE (p + 8 * n) 8) (hu1 : u1 = M.readLE (p + 8 * (n - 1)) 8) (hu0 : u0 = M.readLE (p + 8 * (n - 2)) 8)
    (hdh63 : 2 ^ 63 ≤ dh) (hXD : X < 2 ^ 64 * D) :
    X / D ≤ qhat1 (2 ^ 64) dh dl u2 u1 u0 ∧ qhat1 (2 ^ 64) dh dl u2 u1 u0 ≤ X / D + 1 := by
  obtain ⟨lo, hlo, hD'⟩ := wv_top2 Md dp n hn
  obtain ⟨lo', hlo', hX'⟩ := wv_top3 M p (n + 1) (by omega)
  have e1 : n + 1 - 3 = n - 2 := by omega
  have e2 : n + 1 - 2 = n - 1 := by omega
  have e3 : n + 1 - 1 = n := by omega
  simp only [e1, e2, e3] at hX' hlo'
  rw [← hdh, ← hdl] at hD'
  rw [← hu0, ← hu1, ← hu2] at hX'
  have hB : (0 : Nat) < 2 ^ 64 := by decide
  have hdhB : dh < 2 ^ 64 := by
    rw [hdh]; have := Janus.Arm64.Memory.readLE_lt Md (dp + 8 * (n - 1)) 8; simpa using this
  have hdlB : dl < 2 ^ 64 := by
    rw [hdl]; have := Janus.Arm64.Memory.readLE_lt Md (dp + 8 * (n - 2)) 8; simpa using this
  have hu2B : u2 < 2 ^ 64 := by
    rw [hu2]; have := Janus.Arm64.Memory.readLE_lt M (p + 8 * n) 8; simpa using this
  have hu1B : u1 < 2 ^ 64 := by
    rw [hu1]; have := Janus.Arm64.Memory.readLE_lt M (p + 8 * (n - 1)) 8; simpa using this
  have hu0B : u0 < 2 ^ 64 := by
    rw [hu0]; have := Janus.Arm64.Memory.readLE_lt M (p + 8 * (n - 2)) 8; simpa using this
  have hβ : 0 < 2 ^ (64 * (n - 2)) := Nat.two_pow_pos _
  refine qhat1_bounds (2 ^ 64) dh dl u2 u1 u0 (2 ^ (64 * (n - 2))) D X (by omega) hdhB hdlB hu0B hu1B hu2B hβ ?_ ?_ ?_ ?_ hXD
  · rw [hD, hD']; grind
  · rw [hD, hD']; grind
  · rw [hX, hX']; grind
  · rw [hX, hX']; grind

theorem iter_core (P D X Z u2 qh b r : Nat) (hD : D < P) (hD0 : 0 < D) (hZ : Z < P) (hX : X = u2 * P + Z)
    (hqh : X / D ≤ qh ∧ qh ≤ X / D + 1) (hsub : Z + b * P = r + qh * D) (hr : r < P) :
    (b ≤ u2 ∧ qh = X / D ∧ r = X % D) ∨
    (u2 < b ∧ qh = X / D + 1 ∧ P ≤ r + D ∧ r + D - P = X % D) := by
  have hdm := Nat.div_add_mod X D
  have hml : X % D < D := Nat.mod_lt _ hD0
  obtain ⟨q, hq⟩ : ∃ q, q = X / D := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = X % D := ⟨_, rfl⟩
  rw [← hq, ← hm] at hdm
  rw [← hm] at hml
  rw [← hq] at hqh
  rw [← hq, ← hm]
  have e0 : D * q = q * D := Nat.mul_comm _ _
  have e : (q + 1) * D = q * D + D := by grind
  have hq1 : q * D ≤ u2 * P + Z := by omega
  have hq2 : u2 * P + Z < (q + 1) * D := by omega
  rcases Nat.lt_or_ge u2 b with hb | hb
  · obtain ⟨h1, h2, h3, h4⟩ := knuth_borrow P D u2 Z qh q r b hD hD0 hZ hq1 hq2 hqh hsub hr hb
    right
    refine ⟨hb, h1, h3, ?_⟩
    omega
  · obtain ⟨h1, h2, h3⟩ := knuth_nb P D u2 Z qh q r b hD hD0 hZ hq1 hq2 hqh hsub hr hb
    left
    refine ⟨hb, h1, ?_⟩
    omega

open Janus in
theorem outside_sub (a n a' n' : Nat) (rs : List (Nat × Nat)) (h : Outside a n rs) (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) :
    Outside a' n' rs := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨lo, hi⟩ := r
    simp only [outside_cons] at h ⊢
    obtain ⟨h3, h4⟩ := h
    exact ⟨by omega, ih h4⟩

open Janus in
theorem wv_of_frame (M M' : Janus.Arm64.Memory) (rs : List (Nat × Nat)) (h : MemFrame M M' rs) (p n : Nat)
    (hout : Outside p (8 * n) rs) : wv M' p n = wv M p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [wv_succ, wv_succ, ih (p + 8) (outside_sub _ _ _ _ _ hout (by omega) (by omega)),
      h.readLE p 8 (outside_sub _ _ _ _ _ hout (by omega) (by omega))]

end Fv256.B
