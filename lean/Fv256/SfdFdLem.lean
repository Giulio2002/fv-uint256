import Janus
import Fv256.Util

/-!
# Extracted-free helper lemmas for the `fromDecimal` loop
-/

namespace Fv256.I

open Janus.Arm64 in
/-- the three 16-byte stores that copy the five-word table `multipliers` to the stack -/
theorem tab_word (m m0 : Memory) (e mt : Nat) (he : 48 ≤ e) :
    ∀ k, k < 5 →
      ((((m.writeLE (e - 48) 16 (m0.readLE mt 16)).writeLE (e - 32) 16 (m0.readLE (mt + 16) 16)).writeLE (e - 24) 16
        (m0.readLE (mt + 24) 16)).readLE (e - 48 + 8 * k) 8) = m0.readLE (mt + 8 * k) 8 := by
  have r16 : ∀ a, m0.readLE a 16 = m0.readLE a 8 + 2 ^ 64 * m0.readLE (a + 8) 8 := fun a => by
    rw [show 16 = 8 + 8 from rfl, Memory.readLE_add]
  have l16 : ∀ a, m0.readLE a 8 < 2 ^ 64 := fun a => by
    have := Memory.readLE_lt m0 a 8
    simpa using this
  have h16 : ∀ a, m0.readLE a 16 / 256 ^ 8 % 256 ^ 8 = m0.readLE (a + 8) 8 := fun a => by
    rw [r16]
    have := l16 a
    have := l16 (a + 8)
    have e1 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [e1]
    omega
  have h16' : ∀ a, m0.readLE a 16 / 256 ^ 0 % 256 ^ 8 = m0.readLE a 8 := fun a => by
    rw [r16]
    have := l16 a
    have := l16 (a + 8)
    have e1 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [e1]
    omega
  have ins : ∀ (M : Memory) (a n b k v : Nat), a ≤ b → b + k ≤ a + n → (M.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k :=
    fun M a n b k v h1 h2 => Memory.readLE_writeLE_inside M v h1 h2
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · simp only [Nat.mul_zero, Nat.add_zero]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (e - 48) 16 (e - 48) 8 _ (by omega) (by omega)]
    simpa using h16' mt
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (e - 48) 16 (e - 48 + 8 * 1) 8 _ (by omega) (by omega)]
    have : e - 48 + 8 * 1 - (e - 48) = 8 := by omega
    rw [this, h16 mt]
  · simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (e - 32) 16 (e - 48 + 8 * 2) 8 _ (by omega) (by omega)]
    have : e - 48 + 8 * 2 - (e - 32) = 0 := by omega
    rw [this, h16' (mt + 16)]
  · rw [ins _ (e - 24) 16 (e - 48 + 8 * 3) 8 _ (by omega) (by omega)]
    have : e - 48 + 8 * 3 - (e - 24) = 0 := by omega
    rw [this, h16' (mt + 24)]
  · rw [ins _ (e - 24) 16 (e - 48 + 8 * 4) 8 _ (by omega) (by omega)]
    have : e - 48 + 8 * 4 - (e - 24) = 8 := by omega
    rw [this, h16 (mt + 24)]


open Janus.Arm64 in
/-- the stores of round `0`: `z = {v, 0, 0, 0}` -/
theorem z_store0 (m : Memory) (zz v : Nat) (hv : v < 2 ^ 64) :
    Janus.Spec.val256 (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v) zz = v := by
  have ins : ∀ (M : Memory) (a n b k v : Nat), a ≤ b → b + k ≤ a + n → (M.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k :=
    fun M a n b k v h1 h2 => Memory.readLE_writeLE_inside M v h1 h2
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  unfold Janus.Spec.val256
  rw [Fv256.Util.readLE_32]
  have e1 : (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v).readLE zz 8 = v := by
    rw [Memory.readLE_writeLE_self, h8]; exact Nat.mod_eq_of_lt hv
  have e2 : (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v).readLE (zz + 8) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  have e3 : (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v).readLE (zz + 8 + 8) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 8 + 8) 8 0 (by omega) (by omega)]
    simp
  have e4 : (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v).readLE (zz + 24) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 24) 8 0 (by omega) (by omega)]
    simp
  have e3' : (((m.writeLE (zz + 16) 16 0).writeLE (zz + 8) 8 0).writeLE zz 8 v).readLE (zz + 16) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 16) 8 0 (by omega) (by omega)]
    simp
  rw [e1, e2, e3', e4]
  omega

open Janus.Arm64 in
/-- the stores that build `NewInt(v)` on the stack: `{v, 0, 0, 0}` -/
theorem z_store1 (m : Memory) (zz v : Nat) (hv : v < 2 ^ 64) :
    (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE zz 32 = v := by
  have ins : ∀ (M : Memory) (a n b k v : Nat), a ≤ b → b + k ≤ a + n → (M.writeLE a n v).readLE b k = v / 256 ^ (b - a) % 256 ^ k :=
    fun M a n b k v h1 h2 => Memory.readLE_writeLE_inside M v h1 h2
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  rw [Fv256.Util.readLE_32]
  have e1 : (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE zz 8 = v := by
    rw [Memory.readLE_writeLE_self, h8]; exact Nat.mod_eq_of_lt hv
  have e2 : (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE (zz + 8) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ zz 16 (zz + 8) 8 0 (by omega) (by omega)]; simp
  have e3 : (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE (zz + 8 + 8) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 8 + 8) 8 0 (by omega) (by omega)]; simp
  have e4 : (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE (zz + 24) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 24) 8 0 (by omega) (by omega)]; simp
  have e3' : (((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).readLE (zz + 16) 8 = 0 := by
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [ins _ (zz + 16) 16 (zz + 16) 8 0 (by omega) (by omega)]; simp
  rw [e1, e2, e3', e4]
  omega

open Janus.Arm64 in
theorem z_store2 (m : Memory) (zz v r rv : Nat) (hv : v < 2 ^ 64) (hd : zz + 32 ≤ r ∨ r + 8 ≤ zz) :
    ((((m.writeLE zz 16 0).writeLE (zz + 16) 16 0).writeLE zz 8 v).writeLE r 8 rv).readLE zz 32 = v := by
  rw [Memory.readLE_writeLE_of_disjoint _ _ hd]
  exact z_store1 m zz v hv

end Fv256.I
