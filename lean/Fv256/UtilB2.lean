import Fv256.Spec
import Fv256.Util
import Fv256.UtilB
import Fv256.SpecB2

namespace Fv256.B

theorem wv4_eq (m : Janus.Arm64.Memory) (p : Nat) : wv m p 4 = m.readLE p 32 := by
  rw [Util.readLE_32]
  simp only [wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
  omega

theorem wv_zero2 (m : Janus.Arm64.Memory) (p q : Nat) (h : q = p + 16) :
    wv ((m.writeLE p 16 0).writeLE q 16 0) p 4 = 0 := by
  subst h
  have e1 : ∀ a, p ≤ a → a + 8 ≤ p + 16 → ((m.writeLE p 16 0).writeLE (p + 16) 16 0).readLE a 8 = 0 := by
    intro a h1 h2
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_inside _ _ h1 h2]
    simp
  have e2 : ∀ a, p + 16 ≤ a → a + 8 ≤ p + 32 → ((m.writeLE p 16 0).writeLE (p + 16) 16 0).readLE a 8 = 0 := by
    intro a h1 h2
    rw [Janus.Arm64.Memory.readLE_writeLE_inside _ _ h1 h2]
    simp
  simp only [wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
  rw [e1 p (by omega) (by omega), e1 (p + 8) (by omega) (by omega), e2 (p + 16) (by omega) (by omega), e2 (p + 24) (by omega) (by omega)]

theorem wv_zero2' (m : Janus.Arm64.Memory) (p q : Nat) (h : q = p + 16) :
    wv ((m.writeLE p 16 (BitVec.toNat (0 : BitVec 128))).writeLE q 16 (BitVec.toNat (0 : BitVec 128))) p 4 = 0 := by
  have e : BitVec.toNat (0 : BitVec 128) = 0 := rfl
  rw [e]
  exact wv_zero2 m p q h

theorem bv128_zero_toNat : BitVec.toNat (0 : BitVec 128) = 0 := rfl

theorem or_toNat_zero_iff (a b : BitVec 64) : (a ||| b).toNat = 0 ↔ a.toNat = 0 ∧ b.toNat = 0 := by
  rw [BitVec.toNat_or, Nat.or_eq_zero_iff]

theorem ofNat64_toNat_zero_iff (a : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = 0 ↔ a = 0 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem one_eq_div (x y : Nat) (h : x = y) (hy : y ≠ 0) : 1 = x / y := by
  subst h
  exact (Nat.div_self (Nat.pos_of_ne_zero hy)).symm

theorem borrow_zero_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (h0 : a0 < 18446744073709551616) (h1 : a1 < 18446744073709551616)
    (h2 : a2 < 18446744073709551616) (h3 : a3 < 18446744073709551616) (g0 : b0 < 18446744073709551616)
    (g1 : b1 < 18446744073709551616) (g2 : b2 < 18446744073709551616) (g3 : b3 < 18446744073709551616) :
    (if a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat then 1#64 else 0#64).toNat = 0 ↔
    b0 + 18446744073709551616 * b1 + 340282366920938463463374607431768211456 * b2 +
        6277101735386680763835789423207666416102355444464034512896 * b3 ≤
      a0 + 18446744073709551616 * a1 + 340282366920938463463374607431768211456 * a2 +
        6277101735386680763835789423207666416102355444464034512896 * a3 := by
  have key := Util.lt_chain a0 a1 a2 a3 b0 b1 b2 b3 h0 h1 h2 h3 g0 g1 g2 g3
  by_cases hP : a3 < b3 + (decide (a2 < b2 + (decide (a1 < b1 + (decide (a0 < b0)).toNat)).toNat)).toNat
  · rw [if_pos hP]
    simp only [hP, decide_true] at key
    have hQ := of_decide_eq_true key.symm
    simp only [Nat.not_le.mpr hQ, iff_false]
    decide
  · rw [if_neg hP]
    simp only [hP, decide_false] at key
    have hQ := of_decide_eq_false key.symm
    simp only [Nat.not_lt.mp hQ, iff_true]
    rfl

theorem div_congr (a b c : Nat) (h : b = c) : a / b = a / c := by rw [h]

theorem zero_eq_mod_self (x y : Nat) (h : x = y) : 0 = x % y := by
  subst h
  exact (Nat.mod_self x).symm

theorem mod_congr (a b c : Nat) (h : b = c) : a % b = a % c := by rw [h]

theorem mod64_mod (a b : Nat) (ha : a < 2 ^ 64) : a % b % 18446744073709551616 = a % b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le a b) (by omega))

theorem divSpec_zero_left (y : Nat) : divSpec 0 y = 0 := by
  unfold divSpec; split <;> simp

theorem divSpec_zero_right (x : Nat) : divSpec x 0 = 0 := by
  unfold divSpec; simp

theorem modSpec_zero_left (y : Nat) : modSpec 0 y = 0 := by
  unfold modSpec; split <;> simp

theorem modSpec_zero_right (x : Nat) : modSpec x 0 = 0 := by
  unfold modSpec; simp

theorem steps_link {p : Janus.Amd64.Program} (impl : List Janus.Amd64.Segment) {s s' : Janus.Amd64.State} {k : Nat}
    (h : Janus.Amd64.Program.Steps p s k s') : Janus.Amd64.Program.Steps (p.link impl) s k s' := by
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    exact .step (by simpa using hx) (by simpa using hs) (Janus.Amd64.Program.fetch_link impl hf) hst ih

theorem summary_link {p : Janus.Amd64.Program} (impl : List Janus.Amd64.Segment) {entry : Nat}
    {pre : Janus.Amd64.State → Prop} {post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (h : Janus.Amd64.Tactic.Summary p entry pre post) : Janus.Amd64.Tactic.Summary (p.link impl) entry pre post := by
  intro s hpc hp
  obtain ⟨k, s', hst, hr, hq⟩ := h s hpc hp
  exact ⟨k, s', steps_link impl hst, hr, hq⟩

theorem divSpec_of_ne (x y : Nat) (h : y ≠ 0) : divSpec x y = x / y := by unfold divSpec; simp [h]
theorem modSpec_of_ne (x y : Nat) (h : y ≠ 0) : modSpec x y = x % y := by unfold modSpec; simp [h]

theorem ne_zero_of_limbs (a b c d : Nat) (h : ¬(((a = 0 ∧ b = 0) ∧ c = 0) ∧ d = 0)) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
      6277101735386680763835789423207666416102355444464034512896 * d ≠ 0 := by
  intro h'; apply h; omega

end Fv256.B
