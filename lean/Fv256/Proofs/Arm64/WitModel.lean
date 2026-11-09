import Janus

/-!
# A toy interface model at an arbitrary type address `T` (Extracted-free; for witnesses)

`Janus.Contracts.IfaceModel.R0` fixes its one type `TD` at `0x10000`.  A witness of a theorem that assumes the binary's read-only data
(`DataLoaded`) needs the model's type at the address the binary's data names (`go:itab.internal/strconv.Error,error` has the type
word `0xcfc80`).  `R3 T` is `R0` with the type at `T` (48 bytes of descriptor, private), no interface types and no itabs.
-/

open Janus Janus.Arm64 Janus.Spec Janus.Spec.Map Janus.Spec.Type

namespace Fv256.Arm64.WitModel

/-- the environment: the descriptor of `T` is readable and says: 8 bytes, no pointers, regular memory, not direct -/
def Env3 (T : Nat) (m : Memory) (_ : W64) : Prop :=
  m.accessible T 48 false = true ∧ m.readLE T 8 = 8 ∧ m.readLE (T + 8) 8 = 0 ∧ m.readLE (T + 20) 1 = 8

def R3 (T : Nat) : IfaceModel where
  itab _ _ := none
  eq _ m x y := m.readLE x 8 == m.readLE y 8
  Comparable t m x y := t = T ∧ m.accessible x 8 false = true ∧ m.accessible y 8 false = true
  IsType t := t = T
  IsInter _ := False
  Env := Env3 T
  priv := [(T, T + 48)]
  depth := 64

@[simp] theorem R3_priv (T : Nat) : (R3 T).priv = [(T, T + 48)] := rfl
@[simp] theorem R3_depth (T : Nat) : (R3 T).depth = 64 := rfl
@[simp] theorem R3_isType (T t : Nat) : (R3 T).IsType t = (t = T) := rfl
@[simp] theorem R3_env (T : Nat) (m : Memory) (g : W64) : (R3 T).Env m g = Env3 T m g := rfl
@[simp] theorem R3_eq (T t : Nat) (m : Memory) (x y : Nat) : (R3 T).eq t m x y = (m.readLE x 8 == m.readLE y 8) := rfl
@[simp] theorem R3_comparable (T t : Nat) (m : Memory) (x y : Nat) :
    (R3 T).Comparable t m x y = (t = T ∧ m.accessible x 8 false = true ∧ m.accessible y 8 false = true) := rfl

theorem R3_laws (T : Nat) (h0 : T ≠ 0) (h48 : T + 48 ≤ 2 ^ 48) : (R3 T).Laws where
  env_frame m m' g h ha := by
    obtain ⟨h1, d1, d2, d3⟩ := h
    have hr : ∀ a n, T ≤ a → a + n ≤ T + 48 → m'.readLE a n = m.readLE a n :=
      fun a n h1 h2 => ha.readLE ⟨(T, T + 48), by simp, h1, h2⟩
    exact ⟨by rw [ha.accessible]; exact h1, (hr T 8 (Nat.le_refl _) (by omega)).trans d1,
      (hr (T + 8) 8 (by omega) (by omega)).trans d2, (hr (T + 20) 1 (by omega) (by omega)).trans d3⟩
  type_desc m g t h ht := by
    obtain ⟨h1, -⟩ := h
    simp only [R3_isType] at ht
    subst ht
    exact ⟨h0, h48, h1, ⟨(t, t + 48), by simp, Nat.le_refl _, Nat.le_refl _⟩⟩
  inter_desc m g i h hi := absurd hi (by simp [R3])
  itab_ne i t tab h := by simp [R3] at h
  regular m g t x y h ht hreg hnd hx hy := by
    obtain ⟨-, d1, -, d3⟩ := h
    simp only [R3_isType] at ht
    subst ht
    simp only [tySize, d1] at hx hy ⊢
    exact ⟨⟨rfl, hx, hy⟩, rfl⟩
  direct m g t x y h ht hreg hd := by
    obtain ⟨-, d1, -, d3⟩ := h
    simp only [R3_isType] at ht
    subst ht
    simp only [isDirectIface, tyTFlag, d3] at hd
    exact absurd hd (by decide)

open Janus.Contracts.Iface in
theorem efaceEqual_R3 {T : Nat} {m : Memory} {g : W64} (h : Env3 T m g) (x y : Nat) (hT : T ≠ 0) :
    efaceEqual (R3 T) m T x y = (m.readLE x 8 == m.readLE y 8) := by
  obtain ⟨-, -, -, d3⟩ := h
  have hnd : isDirectIface m T = false := by simp only [isDirectIface, tyTFlag, d3]; decide
  simp only [efaceEqual, hnd]
  simp [hT]

end Fv256.Arm64.WitModel
