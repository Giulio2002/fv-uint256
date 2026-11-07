import Fv256.Util

/-!
# `OnlyWrites3` (FV-SA): a memory that agrees with another outside three byte ranges (Extracted-free)

Used for the arm64 `MulOverflow` library summary with an explicit stack frame: the object `z`, the callee's scratch below the stack
pointer `[sp-240, sp-8)`, and the argument spill slot `[sp+8, sp+16)`.  The two words `[sp-8, sp+8)` (the caller's saved frame
pointer and link register) are NOT in any range: they are preserved.
-/

namespace Fv256.UtilSa

def OnlyWrites3 (m m' : Janus.Arm64.Memory) (p n q k r t : Nat) : Prop :=
  m'.regions = m.regions ∧ ∀ a, (a < p ∨ p + n ≤ a) → (a < q ∨ q + k ≤ a) → (a < r ∨ r + t ≤ a) → m'.bytes a = m.bytes a

theorem ow3_refl (m : Janus.Arm64.Memory) (p n q k r t : Nat) : OnlyWrites3 m m p n q k r t := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem ow3_wl_iff {m m' : Janus.Arm64.Memory} {p n q k r t a j : Nat} (v : Nat)
    (h1 : p ≤ a) (h2 : a + j ≤ p + n) :
    OnlyWrites3 m (m'.writeLE a j v) p n q k r t ↔ OnlyWrites3 m m' p n q k r t :=
  ⟨fun h => ⟨by rw [← Janus.Arm64.Memory.regions_writeLE m' a j v]; exact h.1, fun b hb hb' hb'' => by
      rw [← h.2 b hb hb' hb'', Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => ⟨by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.1, fun b hb hb' hb'' => by
      rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb hb' hb''⟩⟩

theorem ow3_wq_iff {m m' : Janus.Arm64.Memory} {p n q k r t a j : Nat} (v : Nat)
    (h1 : q ≤ a) (h2 : a + j ≤ q + k) :
    OnlyWrites3 m (m'.writeLE a j v) p n q k r t ↔ OnlyWrites3 m m' p n q k r t :=
  ⟨fun h => ⟨by rw [← Janus.Arm64.Memory.regions_writeLE m' a j v]; exact h.1, fun b hb hb' hb'' => by
      rw [← h.2 b hb hb' hb'', Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => ⟨by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.1, fun b hb hb' hb'' => by
      rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb hb' hb''⟩⟩

theorem ow3_wr_iff {m m' : Janus.Arm64.Memory} {p n q k r t a j : Nat} (v : Nat)
    (h1 : r ≤ a) (h2 : a + j ≤ r + t) :
    OnlyWrites3 m (m'.writeLE a j v) p n q k r t ↔ OnlyWrites3 m m' p n q k r t :=
  ⟨fun h => ⟨by rw [← Janus.Arm64.Memory.regions_writeLE m' a j v]; exact h.1, fun b hb hb' hb'' => by
      rw [← h.2 b hb hb' hb'', Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]⟩,
   fun h => ⟨by rw [Janus.Arm64.Memory.regions_writeLE]; exact h.1, fun b hb hb' hb'' => by
      rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]; exact h.2 b hb hb' hb''⟩⟩

theorem ow3_self_iff (m : Janus.Arm64.Memory) (p n q k r t : Nat) : OnlyWrites3 m m p n q k r t ↔ True :=
  ⟨fun _ => trivial, fun _ => ow3_refl m p n q k r t⟩

/-- the frame form -/
theorem ow3_memFrame {m m' : Janus.Arm64.Memory} {p n q k r t : Nat} (h : OnlyWrites3 m m' p n q k r t) :
    Janus.MemFrame m m' [(p, p + n), (q, q + k), (r, r + t)] := by
  refine ⟨fun a n' hout => ?_, fun a n' w => ?_⟩
  · apply Janus.Arm64.Memory.readLE_congr
    intro i hi
    simp only [Janus.outside_cons, Janus.outside_nil, and_true] at hout
    exact (h.2 (a + i) (by omega) (by omega) (by omega)).symm ▸ rfl
  · simp only [Janus.Arm64.Memory.accessible, h.1]

end Fv256.UtilSa
