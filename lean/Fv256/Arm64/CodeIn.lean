import Janus

/-!
# arm64 `CodeIn` for library programs

A library program `p` (a few segments) is `CodeIn` a consumer's extracted program `P` when every segment of `p` occurs in `P`
(same name, base and words), no other segment of `P` overlaps it, and `P` has no stub or exit address inside it.  Summaries
proved about `p` then transfer to `P` with `Janus.Contracts.EqHashModel.Summary.of_codeIn`.
-/

namespace Fv256.Arm64.CodeIn

open Janus Janus.Contracts.EqHashModel

deriving instance DecidableEq for Janus.Segment

/-- the address range of `seg` is disjoint from that of `seg'` -/
def Disj (seg seg' : Segment) : Prop :=
  seg'.base + 4 * seg'.words.length ≤ seg.base ∨ seg.base + 4 * seg.words.length ≤ seg'.base

instance (seg seg' : Segment) : Decidable (Disj seg seg') := by unfold Disj; infer_instance

theorem fetchIn_of_mem (l : List Segment) (seg : Segment) (hm : seg ∈ l)
    (hd : ∀ seg' ∈ l, seg' = seg ∨ Disj seg seg') (pc w : Nat)
    (hr : seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0) (hw : seg.words[(pc - seg.base) / 4]? = some w) :
    Program.fetchIn l pc = some w := by
  induction l with
  | nil => cases hm
  | cons s rest ih =>
    by_cases hs : s = seg
    · subst hs
      simp only [Program.fetchIn]
      rw [if_pos hr, hw]
    · have hdis := (hd s (List.mem_cons_self ..)).resolve_left hs
      have hlen : (pc - seg.base) / 4 < seg.words.length := (List.getElem?_eq_some_iff.1 hw).1
      have hnone : Program.fetchIn (s :: rest) pc = Program.fetchIn rest pc := by
        unfold Disj at hdis
        simp only [Program.fetchIn]
        by_cases hc : s.base ≤ pc ∧ (pc - s.base) % 4 = 0
        · rw [if_pos hc]
          have : s.words[(pc - s.base) / 4]? = none := by
            rw [List.getElem?_eq_none_iff]; omega
          rw [this]
        · rw [if_neg hc]
      have hm' : seg ∈ rest := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm hs
        · exact h
      rw [hnone]
      exact ih hm' (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs'))

theorem fetchIn_some (l : List Segment) (pc w : Nat) (h : Program.fetchIn l pc = some w) :
    ∃ seg ∈ l, seg.base ≤ pc ∧ (pc - seg.base) % 4 = 0 ∧ seg.words[(pc - seg.base) / 4]? = some w := by
  induction l with
  | nil => simp [Program.fetchIn] at h
  | cons s rest ih =>
    simp only [Program.fetchIn] at h
    split at h
    · rename_i hc
      split at h
      · rename_i w' hw'
        cases h
        exact ⟨s, List.mem_cons_self .., hc.1, hc.2, hw'⟩
      · obtain ⟨seg, hseg, hr⟩ := ih h
        exact ⟨seg, List.mem_cons_of_mem _ hseg, hr⟩
    · obtain ⟨seg, hseg, hr⟩ := ih h
      exact ⟨seg, List.mem_cons_of_mem _ hseg, hr⟩

/-- `p` is `CodeIn` `P` when each segment of `p` is a segment of `P`, no other segment of `P` overlaps it, and `P` has no
stub and not its exit address inside it. -/
theorem codeIn_of_sub (p P : Program)
    (hseg : ∀ seg ∈ p.segments, seg ∈ P.segments ∧ ∀ seg' ∈ P.segments, seg' = seg ∨ Disj seg seg')
    (hstub : ∀ seg ∈ p.segments, ∀ st ∈ P.stubs, st.addr < seg.base ∨ seg.base + 4 * seg.words.length ≤ st.addr)
    (hexit : ∀ seg ∈ p.segments, P.exitAddr < seg.base ∨ seg.base + 4 * seg.words.length ≤ P.exitAddr) :
    CodeIn p P := by
  intro pc w hf
  obtain ⟨seg, hsp, hr1, hr2, hw⟩ := fetchIn_some p.segments pc w hf
  obtain ⟨hmem, hdis⟩ := hseg seg hsp
  have hlen : (pc - seg.base) / 4 < seg.words.length := (List.getElem?_eq_some_iff.1 hw).1
  refine ⟨?_, ?_, ?_⟩
  · exact fetchIn_of_mem P.segments seg hmem hdis pc w ⟨hr1, hr2⟩ hw
  · unfold Program.stubAt
    rw [List.find?_eq_none]
    intro st hst
    have := hstub seg hsp st hst
    simp only [decide_eq_true_eq]
    omega
  · have := hexit seg hsp
    omega

end Fv256.Arm64.CodeIn
