import Janus
open Janus Janus.Arm64
namespace Fv256.Arm64.DivMSlots

theorem slots (M : Memory) (sp ret fp z : Nat) (h : 168 ≤ sp) :
    ((((M.writeLE (sp - 160) 8 ret).writeLE (sp - 168) 8 fp).writeLE (sp + 8) 8 z).readLE (sp - 160 - 8) 8 = fp % 2 ^ 64) ∧
    ((((M.writeLE (sp - 160) 8 ret).writeLE (sp - 168) 8 fp).writeLE (sp + 8) 8 z).readLE (sp - 160 + 168) 8 = z % 2 ^ 64) := by
  constructor
  · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), show sp - 160 - 8 = sp - 168 by omega, Memory.readLE_writeLE_self]
  · rw [show sp - 160 + 168 = sp + 8 by omega, Memory.readLE_writeLE_self]

set_option maxHeartbeats 2000000 in
theorem alloc_slots (rt : List (Nat × Nat)) (M0 Mc : Memory) (sp ret fp z x y ptr a b c d : Nat) (h : 4256 ≤ sp)
    (hout : Outside (sp - 4256) (4256 + 40) rt)
    (hdj : ptr + 32 ≤ sp - 4256 ∨ sp + 40 ≤ ptr)
    (cfr : MemFrame ((((((M0.writeLE (sp - 160) 8 ret).writeLE (sp - 168) 8 fp).writeLE (sp + 8) 8 z).writeLE (sp + 16) 8 x).writeLE
        (sp + 24) 8 y).writeLE (sp + 32) 8 z) Mc (rt ++ [(sp - 160 - 4096, sp - 160 - 8), (sp - 160 + 8, sp - 160 + 8 + 8)])) :
    let M' := (((Mc.writeLE ptr 8 a).writeLE (ptr + 8) 8 b).writeLE (ptr + 16) 8 c).writeLE (ptr + 24) 8 d
    M'.readLE (sp - 160) 8 = ret % 2 ^ 64 ∧ M'.readLE (sp - 160 - 8) 8 = fp % 2 ^ 64 ∧ M'.readLE (sp - 160 + 168) 8 = z % 2 ^ 64 := by
  intro M'
  have hOc : ∀ p n, sp - 168 ≤ p → p + n ≤ sp + 40 → Outside p n (rt ++ [(sp - 160 - 4096, sp - 160 - 8), (sp - 160 + 8, sp - 160 + 8 + 8)]) → True := fun _ _ _ _ _ => trivial
  have hO : ∀ p, sp - 168 ≤ p → p + 8 ≤ sp + 40 → (p + 8 ≤ sp - 160 - 4096 ∨ sp - 160 - 8 ≤ p) → (p + 8 ≤ sp - 160 + 8 ∨ sp - 160 + 16 ≤ p) →
      Outside p 8 (rt ++ [(sp - 160 - 4096, sp - 160 - 8), (sp - 160 + 8, sp - 160 + 8 + 8)]) := by
    intro p h1 h2 h3 h4
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    refine ⟨Janus.Outside.of_sub hout (by omega) (by omega), ?_, ?_⟩ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [M']
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [cfr.readLE _ _ (hO (sp - 160) (by omega) (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  · simp only [M']
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [cfr.readLE _ _ (hO (sp - 160 - 8) (by omega) (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    rw [show sp - 160 - 8 = sp - 168 by omega, Memory.readLE_writeLE_self]
  · simp only [M']
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    rw [cfr.readLE _ _ (hO (sp - 160 + 168) (by omega) (by omega) (by omega) (by omega))]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    rw [show sp - 160 + 168 = sp + 8 by omega, Memory.readLE_writeLE_self]

end Fv256.Arm64.DivMSlots
