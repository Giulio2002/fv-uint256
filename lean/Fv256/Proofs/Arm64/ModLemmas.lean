import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Arm64.DivLemmas

open Janus Janus.Arm64 Janus.Tactic

namespace Fv256.Arm64.ModLemmas

/-- The 64-bit fast path of `Mod`: `x0 - (x0 / y0) * y0` computed with wrap-around equals `x0 % y0 = modSpec x0 y` when
the upper limbs of `x` vanish and `0 < y ≤ x`. -/
theorem mfast_close (x0 y0 y1 y2 y3 : Nat) (hx : x0 < 18446744073709551616) (hy0 : y0 ≠ 0)
    (hy : y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
      6277101735386680763835789423207666416102355444464034512896 * y3 ≤ x0) :
    (18446744073709551616 - x0 / y0 * y0 % 18446744073709551616 + x0) % 18446744073709551616 =
      Fv256.B.modSpec x0 (y0 + 18446744073709551616 * y1 + 340282366920938463463374607431768211456 * y2 +
        6277101735386680763835789423207666416102355444464034512896 * y3) := by
  have e : y1 = 0 ∧ y2 = 0 ∧ y3 = 0 := by omega
  obtain ⟨rfl, rfl, rfl⟩ := e
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [Fv256.B.modSpec, if_neg hy0]
  have h1 := Nat.div_add_mod x0 y0
  have h2 := Nat.mod_lt x0 (Nat.pos_of_ne_zero hy0)
  rw [Nat.mul_comm] at h1
  generalize x0 / y0 * y0 = p at *
  generalize x0 % y0 = r at *
  omega

/-- Eleven stores whose targets avoid `[x, x+32)` leave `wv m x 4` unchanged (the `Mod` frame before the call). -/
theorem wv4_chain11 (m : Memory) (sp x v1 v2 v3 : Nat) (h : x + 32 ≤ sp - 488 ∨ sp + 16 ≤ x) (hsp : 488 ≤ sp) :
    Fv256.B.wv (((((((((((m.writeLE (sp - 144) 8 v1).writeLE (sp - 152) 8 v2).writeLE (sp + 8) 8 v3).writeLE (sp - 40) 8 0).writeLE
      (sp - 32) 8 0).writeLE (sp - 24) 8 0).writeLE (sp - 16) 8 0).writeLE (sp - 72) 8 0).writeLE (sp - 64) 8 0).writeLE
      (sp - 56) 8 0).writeLE (sp - 48) 8 0) x 4 = Fv256.B.wv m x 4 := by
  rw [Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega), Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega),
    Fv256.B.wv_writeLE_outside _ _ _ _ _ _ (by omega)]

/-- The eleven pre-call stores of `Mod` stay inside the callee-visible frame windows. -/
theorem chain11_frame (m : Memory) (sp v1 v2 v3 : Nat) (hsp : 488 ≤ sp) :
    Janus.MemFrame m (((((((((((m.writeLE (sp - 144) 8 v1).writeLE (sp - 152) 8 v2).writeLE (sp + 8) 8 v3).writeLE (sp - 40) 8 0).writeLE
      (sp - 32) 8 0).writeLE (sp - 24) 8 0).writeLE (sp - 16) 8 0).writeLE (sp - 72) 8 0).writeLE (sp - 64) 8 0).writeLE
      (sp - 56) 8 0).writeLE (sp - 48) 8 0) [(sp - 488, sp - 8), (sp + 8, sp + 16)] := by
  have r1 : (sp - 488, sp - 8) ∈ [(sp - 488, sp - 8), (sp + 8, sp + 16)] := by simp
  have r2 : (sp + 8, sp + 16) ∈ [(sp - 488, sp - 8), (sp + 8, sp + 16)] := by simp
  exact (((((((((((MemFrame.refl m _).writeLE v1 r1 (by simp <;> omega) (by simp <;> omega)).writeLE v2 r1 (by simp <;> omega) (by simp <;> omega)).writeLE v3 r2 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)).writeLE 0 r1 (by simp <;> omega) (by simp <;> omega)

end Fv256.Arm64.ModLemmas
