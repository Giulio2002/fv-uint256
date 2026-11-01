import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UdivMathB

namespace Fv256.B

theorem norm_div_eq (U D t Q Rn : Nat) (ht : 0 < t) (hD : 0 < D) (h : U * t = D * t * Q + Rn) (hR : Rn < D * t) :
    Q = U / D ∧ Rn = (U % D) * t := by
  have h1 : D * Q * t ≤ U * t := by
    have : D * Q * t = D * t * Q := by grind
    omega
  have h2 : D * Q ≤ U := Nat.le_of_mul_le_mul_right h1 ht
  obtain ⟨r, hr⟩ : ∃ r, U = D * Q + r := ⟨U - D * Q, by omega⟩
  have h3 : Rn = r * t := by
    have : U * t = D * Q * t + r * t := by rw [hr]; grind
    have e : D * Q * t = D * t * Q := by grind
    omega
  have h4 : r < D := by
    have : r * t < D * t := by omega
    exact Nat.lt_of_mul_lt_mul_right this
  have hq := (Nat.div_mod_unique (a := U) (b := D) (d := Q) (c := r) hD).2 ⟨by omega, h4⟩
  obtain ⟨hq1, hq2⟩ := hq
  exact ⟨hq1.symm, by rw [hq2, h3]⟩

theorem wv_ext (M : Janus.Arm64.Memory) (p k : Nat) :
    ∀ N, k ≤ N → (∀ j, k ≤ j → j < N → M.readLE (p + 8 * j) 8 = 0) → wv M p N = wv M p k := by
  intro N
  induction N with
  | zero => intro hk _; have : k = 0 := by omega
            subst this; rfl
  | succ N ih =>
    intro hk h
    rcases Nat.eq_or_lt_of_le hk with e | e
    · rw [e]
    · rw [wv_snoc, h N (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
      exact ih (by omega) (fun j h1 h2 => h j h1 (by omega))

theorem wv_ge_top (M : Janus.Arm64.Memory) (p n : Nat) (hn : 1 ≤ n) :
    M.readLE (p + 8 * (n - 1)) 8 * 2 ^ (64 * (n - 1)) ≤ wv M p n := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [wv_snoc]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]; omega

theorem dn_norm (Md Mn : Janus.Arm64.Memory) (dp q n s dtop : Nat) (hn1 : 1 ≤ n) (hs : s ≤ 63)
    (hdtop : Md.readLE (dp + 8 * (n - 1)) 8 = dtop) (hn2 : 2 ^ 63 ≤ dtop * 2 ^ s) (hn3 : dtop * 2 ^ s < 2 ^ 64)
    (hdn : ∀ k, k < n → Mn.readLE (q + 8 * k) 8 = (Md.readLE (dp + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + shc Md dp s k) :
    wv Mn q n = wv Md dp n * 2 ^ s ∧ 2 ^ 63 ≤ Mn.readLE (q + 8 * (n - 1)) 8 := by
  have h := shl_vec Md Mn dp q s n (by omega) hdn n (Nat.le_refl _)
  have hc : shc Md dp s n = 0 := by
    unfold shc
    rw [if_neg (by omega), hdtop]
    apply Nat.div_eq_of_lt
    have e64 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
    have h3 := hn3
    rw [e64] at h3
    exact Nat.lt_of_mul_lt_mul_left (a := 2 ^ s) (by rw [Nat.mul_comm (2 ^ s) dtop]; exact h3)
  rw [hc] at h
  refine ⟨by simpa using h, ?_⟩
  rw [hdn (n - 1) (by omega)]
  have hlt : dtop * 2 ^ s % 2 ^ 64 = dtop * 2 ^ s := Nat.mod_eq_of_lt hn3
  rw [hdtop, hlt]
  omega

theorem un_norm (Mu Mn : Janus.Arm64.Memory) (up q ulen s : Nat) (hu1 : 1 ≤ ulen) (hs : s ≤ 63)
    (hun : ∀ k, k < ulen → Mn.readLE (q + 8 * k) 8 = (Mu.readLE (up + 8 * k) 8 * 2 ^ s) % 2 ^ 64 + shc Mu up s k)
    (htop : Mn.readLE (q + 8 * ulen) 8 = Mu.readLE (up + 8 * (ulen - 1)) 8 / 2 ^ (64 - s)) :
    wv Mn q (ulen + 1) = wv Mu up ulen * 2 ^ s := by
  have h := shl_vec Mu Mn up q s ulen (by omega) hun ulen (Nat.le_refl _)
  have hc : shc Mu up s ulen = Mn.readLE (q + 8 * ulen) 8 := by
    unfold shc; rw [if_neg (by omega), htop]
  rw [hc] at h
  rw [wv_snoc]
  have := Nat.mul_comm (Mn.readLE (q + 8 * ulen) 8) (2 ^ (64 * ulen))
  omega

theorem knuth_pre_lt (Mn : Janus.Arm64.Memory) (q ulen n s U Dn : Nat) (hn : 1 ≤ n) (hnu : n ≤ ulen) (hs : s ≤ 63)
    (hUlt : U < 2 ^ (64 * ulen)) (hUn : wv Mn q (ulen + 1) = U * 2 ^ s) (hD : 2 ^ 63 * 2 ^ (64 * (n - 1)) ≤ Dn) :
    wv Mn (q + 8 * (ulen + 1 - n)) n < Dn := by
  have h := wv_top_div Mn q (ulen + 1) (ulen + 1 - n) (by omega)
  rw [show ulen + 1 - (ulen + 1 - n) = n by omega] at h
  rw [h, hUn]
  have e : 2 ^ (64 * ulen) = 2 ^ (64 * (ulen + 1 - n)) * 2 ^ (64 * (n - 1)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have h1 : U * 2 ^ s < 2 ^ (64 * (ulen + 1 - n)) * (2 ^ (64 * (n - 1)) * 2 ^ s) := by
    calc U * 2 ^ s < 2 ^ (64 * ulen) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hUlt (Nat.two_pow_pos _)
      _ = _ := by rw [e]; grind
  have h2 := Nat.div_lt_of_lt_mul h1
  have h3 : 2 ^ (64 * (n - 1)) * 2 ^ s ≤ 2 ^ 63 * 2 ^ (64 * (n - 1)) := by
    rw [Nat.mul_comm (2 ^ 63)]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega : s ≤ 63))
  omega

end Fv256.B
