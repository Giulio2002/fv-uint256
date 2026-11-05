import Fv256.UtilB
import Fv256.UdivremMath

namespace Fv256.F
open Fv256.B

/-- more words never decrease the number -/
theorem wv_mono (M : Janus.Arm64.Memory) (p : Nat) : ∀ m n, m ≤ n → wv M p m ≤ wv M p n := by
  intro m n h
  induction n with
  | zero => have : m = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with e | e
    · rw [e]; exact Nat.le_refl _
    · have := ih (by omega)
      rw [wv_snoc]; omega

/-- if `L` words hold the same number as the first `u ≤ k ≤ L` words, then so do `k` words -/
theorem wv_trunc (M : Janus.Arm64.Memory) (p u k L : Nat) (hu : u ≤ k) (hk : k ≤ L)
    (h : wv M p L = wv M p u) : wv M p k = wv M p u := by
  have h1 := wv_mono M p u k hu
  have h2 := wv_mono M p k L hk
  omega

end Fv256.F
