import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.Arm64.MulModLem

/-!
# amd64 `MulMod` glue: small Extracted-free lemmas (the generic ones are in `Fv256.Arm64.MulModLem`)
-/

open Janus Janus.Arm64

namespace Fv256.Amd64.MulModLemA

/-- the overlapping 16-byte copies `[a,a+16) [a+16,a+32) [a+24,a+40)` -> `b..` read back as one 40-byte read -/
theorem copy40x (M : Memory) (a a1 a2 b b1 b2 : Nat)
    (ha1 : a1 = a + 16) (ha2 : a2 = a + 24) (hb1 : b1 = b + 16) (hb2 : b2 = b + 24)
    (hd : a + 40 ≤ b ∨ b + 40 ≤ a) :
    ((((M.writeLE b 16 (M.readLE a 16)).writeLE b1 16 (M.readLE a1 16)).writeLE b2 16 (M.readLE a2 16))).readLE b 40 = M.readLE a 40 := by
  subst ha1 ha2 hb1 hb2
  have e : ∀ (N : Memory) (c : Nat), N.readLE c 40 = N.readLE c 16 + 256 ^ 16 * N.readLE (c + 16) 8 + 256 ^ 24 * N.readLE (c + 24) 16 := by
    intro N c
    rw [show (40 : Nat) = 16 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show (24 : Nat) = 8 + 16 from rfl,
      Janus.Arm64.Memory.readLE_add]
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.pow_add]
    omega
  rw [e, e M a]
  have l0 := Janus.Arm64.Memory.readLE_lt M a 16
  have l2 := Janus.Arm64.Memory.readLE_lt M (a + 24) 16
  have m1 := Janus.Arm64.Memory.readLE_mod M (a + 16) 16 8 (by omega)
  have r0 : (((M.writeLE b 16 (M.readLE a 16)).writeLE (b + 16) 16 (M.readLE (a + 16) 16)).writeLE (b + 24) 16 (M.readLE (a + 24) 16)).readLE b 16 = M.readLE a 16 := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using l0)
  have r1 : (((M.writeLE b 16 (M.readLE a 16)).writeLE (b + 16) 16 (M.readLE (a + 16) 16)).writeLE (b + 24) 16 (M.readLE (a + 24) 16)).readLE (b + 16) 8 = M.readLE (a + 16) 8 := by
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_inside _ _ (by omega) (by omega)]
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one]
    simpa using m1
  have r2 : (((M.writeLE b 16 (M.readLE a 16)).writeLE (b + 16) 16 (M.readLE (a + 16) 16)).writeLE (b + 24) 16 (M.readLE (a + 24) 16)).readLE (b + 24) 16 = M.readLE (a + 24) 16 := by
    rw [Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using l2)
  rw [r0, r1, r2]

theorem sub312_8 (a : Nat) (h : 312 ≤ a) : a - 312 + 8 = a - 304 := by omega

/-- `Mod` path (amd64 branch-condition shape): the high four product words vanish -/
theorem tail_modA (M : Memory) (p q0 q1 q2 q3 q4 q5 q6 q7 Z X Y m0 m1 m2 : Nat)
    (hw : Fv256.B.wv M p 8 = X * Y)
    (hz : ((M.readLE q4 8 = 0 ∧ M.readLE q5 8 = 0) ∧ M.readLE q6 8 = 0) ∧ M.readLE q7 8 = 0)
    (h : Z = Fv256.B.modSpec (M.readLE q0 8 + 2 ^ 64 * M.readLE q1 8 + 2 ^ 128 * M.readLE q2 8 + 2 ^ 192 * M.readLE q3 8)
      (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2))
    (e1 : q1 = p + 8) (e2 : q2 = p + 16) (e3 : q3 = p + 24) (e4 : q4 = p + 32) (e5 : q5 = p + 40) (e6 : q6 = p + 48)
    (e7 : q7 = p + 56) (e0 : q0 = p) :
    Z = Fv256.F.mulmodSpec X Y (m0 + 2 ^ 64 * m1 + 2 ^ 128 * m2) :=
  Fv256.Arm64.MulModLem.tail_mod M p q0 q1 q2 q3 q4 q5 q6 q7 Z X Y m0 m1 m2 hw
    (by obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hz; exact ⟨⟨c, a, b⟩, d⟩) h e1 e2 e3 e4 e5 e6 e7 e0

theorem nz3A (a b c d : Nat) (h : ¬(((b = 0 ∧ a = 0) ∧ c = 0) ∧ d = 0)) (h3 : d = 0) :
    a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c ≠ 0 := by omega

end Fv256.Amd64.MulModLemA
