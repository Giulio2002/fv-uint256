import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF
import Fv256.UtilB2

/-!
# arm64 `MulMod` glue: small Extracted-free lemmas
-/

open Janus Janus.Arm64

namespace Fv256.Arm64.MulModLem

theorem readLE_40 (m : Memory) (a : Nat) :
    m.readLE a 40 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 +
      2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 := by
  rw [show 40 = 32 + 8 from rfl, Janus.Arm64.Memory.readLE_add, Fv256.Util.readLE_32]

/-- five word copies `[a, a+40) -> [b, b+40)` read back as one 40-byte read -/
theorem copy40 (M : Memory) (a a1 a2 a3 a4 b b1 b2 b3 b4 : Nat)
    (ha1 : a1 = a + 8) (ha2 : a2 = a + 16) (ha3 : a3 = a + 24) (ha4 : a4 = a + 32)
    (hb1 : b1 = b + 8) (hb2 : b2 = b + 16) (hb3 : b3 = b + 24) (hb4 : b4 = b + 32)
    (hd : a + 40 ≤ b ∨ b + 40 ≤ a) :
    (((((M.writeLE b 8 (M.readLE a 8)).writeLE b1 8 (M.readLE a1 8)).writeLE b2 8 (M.readLE a2 8)).writeLE b3 8
      (M.readLE a3 8)).writeLE b4 8 (M.readLE a4 8)).readLE b 40 = M.readLE a 40 := by
  subst ha1 ha2 ha3 ha4 hb1 hb2 hb3 hb4
  rw [readLE_40, readLE_40 M a]
  have h0 := Janus.Arm64.Memory.readLE_lt M a 8
  have h1 := Janus.Arm64.Memory.readLE_lt M (a + 8) 8
  have h2 := Janus.Arm64.Memory.readLE_lt M (a + 16) 8
  have h3 := Janus.Arm64.Memory.readLE_lt M (a + 24) 8
  have h4 := Janus.Arm64.Memory.readLE_lt M (a + 32) 8
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    Nat.reducePow, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]

theorem sub320_8 (a : Nat) (h : 320 ≤ a) : a - 320 + 8 = a - 312 := by omega

theorem ge192 (a b c d : Nat) (h : d ≠ 0) :
    (6277101735386680763835789423207666416102355444464034512896 ≤
      a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
        6277101735386680763835789423207666416102355444464034512896 * d) ↔ True := by
  simp only [iff_true]
  have : 1 ≤ d := Nat.pos_of_ne_zero h
  omega

theorem wv8_eq (M : Memory) (p : Nat) : Fv256.B.wv M p 8 = M.readLE p 64 := by
  rw [show 64 = 32 + 32 from rfl, Janus.Arm64.Memory.readLE_add, show (8 : Nat) = 4 + 4 from rfl]
  have h1 : Fv256.B.wv M p (4 + 4) = Fv256.B.wv M p 4 + 2 ^ 256 * Fv256.B.wv M (p + 32) 4 := by
    simp only [Fv256.B.wv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]
    omega
  rw [h1, Fv256.B.wv4_eq, Fv256.B.wv4_eq]

/-- `reduce4` path: `z = (p mod m)`, `p = x*y`, `m ≠ 0` -/
theorem tail_r4 (M : Memory) (p Z X Y D : Nat) (hD : D ≠ 0) (hw : Fv256.B.wv M p 8 = X * Y)
    (h : Z = M.readLE p 64 % D) : Z = Fv256.F.mulmodSpec X Y D := by
  rw [← wv8_eq, hw] at h
  simp only [Fv256.F.mulmodSpec, if_neg hD]
  exact h

/-- `Mod` path: the high four product words vanish -/
theorem tail_mod (M : Memory) (p q0 q1 q2 q3 q4 q5 q6 q7 Z X Y m0 m1 m2 : Nat)
    (hw : Fv256.B.wv M p 8 = X * Y)
    (hz : (M.readLE q6 8 = 0 ∧ M.readLE q4 8 = 0 ∧ M.readLE q5 8 = 0) ∧ M.readLE q7 8 = 0)
    (h : Z = Fv256.B.modSpec (M.readLE q0 8 + 2 ^ 64 * M.readLE q1 8 + 2 ^ 128 * M.readLE q2 8 + 2 ^ 192 * M.readLE q3 8)
      (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2))
    (e1 : q1 = p + 8) (e2 : q2 = p + 16) (e3 : q3 = p + 24) (e4 : q4 = p + 32) (e5 : q5 = p + 40) (e6 : q6 = p + 48)
    (e7 : q7 = p + 56) (e0 : q0 = p) :
    Z = Fv256.F.mulmodSpec X Y (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2) := by
  subst e1 e2 e3 e4 e5 e6 e7 e0
  obtain ⟨⟨h6, h4, h5⟩, h7⟩ := hz
  have hw' : M.readLE q0 8 + 2 ^ 64 * M.readLE (q0 + 8) 8 + 2 ^ 128 * M.readLE (q0 + 16) 8 + 2 ^ 192 * M.readLE (q0 + 24) 8 = X * Y := by
    simp only [Fv256.B.wv, h4, h5, h6, h7, Nat.add_assoc, Nat.reduceAdd] at hw
    omega
  simp only [Fv256.F.mulmodSpec, Fv256.B.modSpec] at h ⊢
  rw [h, ← hw']

/-- `udivrem` path -/
theorem tail_udiv (M1 M : Memory) (p a a1 a2 a3 b1 b2 b3 X Y D : Nat) (hD : D ≠ 0)
    (hw : Fv256.B.wv M1 p 8 = X * Y)
    (hrem : M.readLE a 8 + 2 ^ 64 * M.readLE a1 8 + 2 ^ 128 * M.readLE a2 8 + 2 ^ 192 * M.readLE a3 8 = Fv256.B.wv M1 p 8 % D)
    (e1 : a1 = a + 8) (e2 : a2 = a + 16) (e3 : a3 = a + 24) (f1 : b1 = a + 8) (f2 : b2 = a + 16) (f3 : b3 = a + 24) :
    M.readLE a 8 + 2 ^ 64 * M.readLE b1 8 + 2 ^ 128 * M.readLE b2 8 + 2 ^ 192 * M.readLE b3 8 = Fv256.F.mulmodSpec X Y D := by
  subst e1 e2 e3 f1 f2 f3
  simp only [Fv256.F.mulmodSpec, if_neg hD]
  rw [← hw]
  exact hrem

theorem nz4 (a b c d : Nat) (h : d ≠ 0) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
      6277101735386680763835789423207666416102355444464034512896 * d ≠ 0 := by omega

theorem nz3 (a b c : Nat) (h : ¬(c = 0 ∧ b = 0 ∧ a = 0)) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c ≠ 0 := by omega

theorem nz3' (a b c d : Nat) (h : ¬(d = 0 ∧ c = 0 ∧ b = 0 ∧ a = 0)) (h3 : d = 0) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c ≠ 0 := by omega

end Fv256.Arm64.MulModLem
