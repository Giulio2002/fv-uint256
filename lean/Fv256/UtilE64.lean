import Janus

open Janus Janus.Arm64 Janus.Tactic

namespace Fv256.E

/-- Sequential composition of two arm64 `ReachesRet` runs (the first ends at `t1`). -/
theorem reachesRet64_bind {p : Janus.Program} {t1 t2 : W64} {s : State}
    {Q1 Q2 : State → Prop} (h : ReachesRet p t1 s Q1)
    (h2 : ∀ s', s'.pc = t1 → Q1 s' → ReachesRet p t2 s' Q2) : ReachesRet p t2 s Q2 := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  obtain ⟨k', s'', hst', hr', hq'⟩ := h2 s' hr hq
  exact ⟨k + k', s'', hst.trans hst', hr', hq'⟩

theorem reachesRet64_mono {p : Janus.Program} {t : W64} {s : State} {Q Q' : State → Prop}
    (h : ReachesRet p t s Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p t s Q' := by
  obtain ⟨k, s', hst, hr, hq⟩ := h
  exact ⟨k, s', hst, hr, hQ s' hq⟩

/-- A frame inside the buffer `[ptr, ptr+len)` keeps the two saved words at `sp-8` and `sp` and their accessibility. -/
theorem stack_pres64 {m m' : Janus.Arm64.Memory} {lo hi ptr len sp : Nat} (hf : MemFrame m m' [(lo, hi)])
    (h1 : ptr ≤ lo) (h2 : hi ≤ ptr + len) (hout : ptr + len ≤ sp - 8 ∨ sp + 16 ≤ ptr) (h8 : 8 ≤ sp) :
    m'.readLE (sp - 8) 8 = m.readLE (sp - 8) 8 ∧ m'.readLE sp 8 = m.readLE sp 8 ∧
      m'.accessible (sp - 8) 16 false = m.accessible (sp - 8) 16 false := by
  refine ⟨hf.readLE _ _ (by simp only [Outside, and_true]; omega), hf.readLE _ _ (by simp only [Outside, and_true]; omega),
    hf.accessible _ _ _⟩

end Fv256.E
