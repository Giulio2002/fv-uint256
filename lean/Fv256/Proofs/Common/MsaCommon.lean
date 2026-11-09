import Janus
import Fv256.Spec.MsaCommon

/-!
# `MarshalSSZAppend`: the ISA-independent budget bound (four 8-byte `append`s)
-/

open Janus Janus.Spec Janus.Contracts

namespace Fv256.Msa

theorem cost_le (len0 len cc : Nat) (h1 : len + 8 ≤ len0 + 32) (h2 : cc < len + 8) :
    roundupsize (nextslicecap (len + 8) cc) true ≤ Kc len0 := by
  have h3 := nextslicecap_le (len + 8) cc h2
  have h4 := roundupsize_le (nextslicecap (len + 8) cc) true
  unfold Kc
  omega

/-- Wrapper that keeps a hypothesis out of the stepping tactics' reach (a visible `MemFrame s.mem S.mem _` makes the store step stuck). -/
def Hidden (p : Prop) : Prop := p

/-- `readLE` only depends on the bytes, also across two addresses. -/
theorem readLE_bytes_shift (m m' : Janus.Arm64.Memory) (a a' n : Nat)
    (h : ∀ i, i < n → m.bytes (a + i) = m'.bytes (a' + i)) : m.readLE a n = m'.readLE a' n := by
  induction n generalizing a a' with
  | zero => rfl
  | succ n ih =>
    rw [Janus.Arm64.Memory.readLE_succ, Janus.Arm64.Memory.readLE_succ]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0, ih (a + 1) (a' + 1) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show a + (i + 1) = a + 1 + i by omega, show a' + (i + 1) = a' + 1 + i by omega] at this)]

/-- One more limb written after the `n` bytes already in place: the (little-endian) read of `n + 8` bytes. -/
theorem mid_step (m0 s : Janus.Arm64.Memory) (a n z v : Nat)
    (hmid : m0.readLE a n = s.readLE z n) (hv : v % 256 ^ 8 = s.readLE (z + n) 8) :
    (m0.writeLE (a + n) 8 v).readLE a (n + 8) = s.readLE z (n + 8) := by
  rw [Janus.Arm64.Memory.readLE_add, Janus.Arm64.Memory.readLE_add s, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (Or.inl (Nat.le_refl _)),
    Janus.Arm64.Memory.readLE_writeLE_self, hmid, hv]

/-- The arithmetic side conditions of a `growslice` call made by block `k` (stated once, over a tiny context, so that
`omega` stays cheap: in the block lemma's context the many `Apart` disjunctions make it exponential). -/
theorem grow_pre (len cc pp len0 b sp : Nat) (hlc : len ≤ cc) (hlle : len + 8 ≤ len0 + 32) (hl0b : len0 < 2 ^ 40)
    (hPb : pp + cc ≤ 2 ^ 48) (hdj : Apart pp cc (sp - 4208) 4232) (hb' : 4208 ≤ sp)
    (hcostK : roundupsize (nextslicecap (len + 8) cc) true ≤ Kc len0) (hK : Kc len0 ≤ b)
    (x : Nat) (hgb : x + 4208 < sp) :
    x + 4096 < sp - 112 ∧ len ≤ cc ∧ len + 8 < 70368744177664 ∧ pp + len ≤ 281474976710656 ∧
      (pp + len ≤ sp - 112 - 4096 ∨ sp - 112 ≤ pp) ∧ (pp + len ≤ sp - 112 + 8 ∨ sp - 112 + 8 + 40 ≤ pp) ∧
      roundupsize (nextslicecap (len + 8) cc) true ≤ b :=
  by
  unfold Apart at hdj
  exact ⟨by omega, hlc, by omega, by omega, by omega, by omega, Nat.le_trans hcostK hK⟩

/-- arm64 twin of `grow_pre` (the callee window is `[sp - 128 - 4096, sp - 128 + 48)` and the block's frame is
`[sp - 4232, sp + 40)`). -/
theorem grow_pre_a64 (len cc pp sp : Nat) (hlc : len ≤ cc) (hPb : pp + cc ≤ 2 ^ 48)
    (hdj : Apart pp cc (sp - 4232) 4272) (hb' : 4232 ≤ sp) :
    len ≤ cc ∧ pp + len ≤ 281474976710656 ∧
      (pp + len ≤ sp - 128 - 4096 ∨ sp - 128 - 8 ≤ pp) ∧ (pp + len ≤ sp - 128 + 8 ∨ sp - 128 + 8 + 40 ≤ pp) := by
  unfold Apart at hdj
  exact ⟨hlc, by omega, by omega, by omega⟩

end Fv256.Msa
