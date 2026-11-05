import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilB2
import Fv256.KnuthMathB

open Janus Janus.Arm64
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Arm64.DivMGlue

set_option maxHeartbeats 1000000 in
theorem glue (rt : List (Nat × Nat)) (sp0 z x y m' ret fp : Nat) (M0 Mst MM M' : Memory)
    (hb : 4256 ≤ sp0)
    (hxo : Outside x 32 rt) (hyo : Outside y 32 rt)
    (hdx : x + 32 ≤ sp0 - 4256 ∨ sp0 + 40 ≤ x) (hdy : y + 32 ≤ sp0 - 4256 ∨ sp0 + 40 ≤ y)
        (hfr : MemFrame M0 Mst (rt ++ [(sp0 - 4256, sp0 + 40)]))
    (hMMf : MemFrame Mst MM [((sp0 - 160) + 80, (sp0 - 160) + 152)])
    (hMM144 : MM.readLE ((sp0 - 160) + 144) 8 = m')
    (hF : MemFrame MM M' [((sp0 - 160) + 112, (sp0 - 160) + 112 + 32), ((sp0 - 160) + 80, (sp0 - 160) + 80 + 32), ((sp0 - 160) - 344, (sp0 - 160) - 8), ((sp0 - 160) + 8, (sp0 - 160) + 72)])
    (hs0 : Mst.readLE (sp0 - 160) 8 = ret) (hs1 : Mst.readLE ((sp0 - 160) - 8) 8 = fp) (hs2 : Mst.readLE ((sp0 - 160) + 168) 8 = z) :
    MemFrame M0 M' (rt ++ [(sp0 - 4256, sp0 + 40)]) ∧
    MemFrame M0 M' (rt ++ [(z, z + 32), (m', m' + 32), (sp0 - 4256, sp0 + 40)]) ∧
    M'.readLE (sp0 - 160) 8 = ret ∧ M'.readLE ((sp0 - 160) - 8) 8 = fp ∧
    M'.readLE ((sp0 - 160) + 168) 8 = z ∧ M'.readLE ((sp0 - 160) + 144) 8 = m' ∧
    Fv256.B.wv MM x 4 = Fv256.B.wv M0 x 4 ∧ Fv256.B.wv MM y 4 = Fv256.B.wv M0 y 4 := by
  have hout : ∀ p, Outside p 32 rt → (p + 32 ≤ sp0 - 4256 ∨ sp0 + 40 ≤ p) → Outside p 32 (rt ++ [(sp0 - 4256, sp0 + 40)]) := by
    intro p h1 h2
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
    exact ⟨h1, h2⟩
  have hMst : ∀ p, Outside p 32 rt → (p + 32 ≤ sp0 - 4256 ∨ sp0 + 40 ≤ p) → Fv256.B.wv Mst p 4 = Fv256.B.wv M0 p 4 :=
    fun p h1 h2 => (Fv256.B.wv_of_frame M0 Mst _ hfr p 4 (by
      have h3 := hout p h1 h2
      exact (by simpa using h3 : Outside p (8 * 4) (rt ++ [(sp0 - 4256, sp0 + 40)]))))
  have hMM : ∀ p, (p + 32 ≤ sp0 - 160 + 80 ∨ sp0 - 160 + 152 ≤ p) → Fv256.B.wv MM p 4 = Fv256.B.wv Mst p 4 := by
    intro p h
    exact Fv256.B.wv_of_frame Mst MM _ hMMf p 4 (by simp [Outside] <;> omega)
  have h1 : MemFrame M0 MM (rt ++ [(sp0 - 4256, sp0 + 40)]) := hfr.trans hMMf (by
    intro a n h
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    exact ⟨⟨h.1, h.2⟩, by omega⟩)
  have h2 : MemFrame M0 M' (rt ++ [(sp0 - 4256, sp0 + 40)]) := h1.trans hF (by
    intro a n h
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    exact ⟨h, by omega⟩)
  have h3 : MemFrame MM M' [(sp0 - 160 + 112, sp0 - 160 + 112 + 32), (sp0 - 160 + 80, sp0 - 160 + 80 + 32), (sp0 - 160 - 344, sp0 - 160 - 8), (sp0 - 160 + 8, sp0 - 160 + 72)] := hF
  refine ⟨h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine h2.mono ?_
    intro a n h
    simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
    exact ⟨h.1, h.2.2.2⟩
  · rw [hF.readLE _ _ (by simp [Outside] <;> omega), hMMf.readLE _ _ (by simp [Outside] <;> omega)]; exact hs0
  · rw [hF.readLE _ _ (by simp [Outside] <;> omega), hMMf.readLE _ _ (by simp [Outside] <;> omega)]; exact hs1
  · rw [hF.readLE _ _ (by simp [Outside] <;> omega), hMMf.readLE _ _ (by simp [Outside] <;> omega)]; exact hs2
  · rw [hF.readLE _ _ (by simp [Outside] <;> omega)]; exact hMM144
  · exact hMM x (by omega) |>.trans (hMst x hxo hdx)
  · exact hMM y (by omega) |>.trans (hMst y hyo hdy)
end Fv256.Arm64.DivMGlue
