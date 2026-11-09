import Janus
import Fv256.Proofs.Common.UtilB2

/-!
# `CodeIn64` for library programs

A library program `p` (a few segments) is `CodeIn64` of a consumer's extracted program `P` when every segment of `p`
occurs in `P` (same name, base and bytes), no other segment of `P` overlaps it, `P` has no stub or exit address inside
it.  Summaries proved about `p` then transfer to `P` with `Janus.Contracts.EqHashModel.Summary.of_codeIn64`.
-/

namespace Fv256.CodeIn

open Janus.Amd64

deriving instance DecidableEq for Janus.Amd64.Segment

/-- the address range of `seg` is disjoint from that of `seg'` -/
def Disj (seg seg' : Segment) : Prop :=
  seg'.base + seg'.bytes.length ≤ seg.base ∨ seg.base + seg.bytes.length ≤ seg'.base

instance (seg seg' : Segment) : Decidable (Disj seg seg') := by unfold Disj; infer_instance

theorem fetchIn_of_mem (l : List Segment) (seg : Segment) (hm : seg ∈ l)
    (hd : ∀ seg' ∈ l, seg' = seg ∨ Disj seg seg') (pc : Nat) (hr : seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length) :
    Program.fetchIn l pc = some ((seg.bytes.drop (pc - seg.base)).take 15) := by
  induction l with
  | nil => cases hm
  | cons s rest ih =>
    simp only [Program.fetchIn]
    by_cases hs : s = seg
    · subst hs
      rw [if_pos hr]
    · have hdis := (hd s (List.mem_cons_self ..)).resolve_left hs
      have hnot : ¬ (s.base ≤ pc ∧ pc < s.base + s.bytes.length) := by
        unfold Disj at hdis; omega
      rw [if_neg hnot]
      have hm' : seg ∈ rest := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm hs
        · exact h
      exact ih hm' (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs'))

theorem fetchIn_some (l : List Segment) (pc : Nat) (w : List Nat) (h : Program.fetchIn l pc = some w) :
    ∃ seg ∈ l, (seg.base ≤ pc ∧ pc < seg.base + seg.bytes.length) ∧ w = (seg.bytes.drop (pc - seg.base)).take 15 := by
  induction l with
  | nil => simp [Program.fetchIn] at h
  | cons s rest ih =>
    simp only [Program.fetchIn] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨s, List.mem_cons_self .., hc, rfl⟩
    · obtain ⟨seg, hseg, hr, hw⟩ := ih h
      exact ⟨seg, List.mem_cons_of_mem _ hseg, hr, hw⟩

/-- `p` is `CodeIn64` of `P` when each segment of `p` is a segment of `P`, no other segment of `P` overlaps it, and `P` has no
stub and not its exit address inside it. -/
theorem codeIn64_of_sub (p P : Janus.Amd64.Program)
    (hseg : ∀ seg ∈ p.segments, seg ∈ P.segments ∧ ∀ seg' ∈ P.segments, seg' = seg ∨ Disj seg seg')
    (hstub : ∀ seg ∈ p.segments, ∀ st ∈ P.stubs, st.addr < seg.base ∨ seg.base + seg.bytes.length ≤ st.addr)
    (hexit : ∀ seg ∈ p.segments, P.exitAddr < seg.base ∨ seg.base + seg.bytes.length ≤ P.exitAddr) :
    Janus.Contracts.EqHashModel.CodeIn64 p P := by
  intro pc w hf
  obtain ⟨seg, hsp, hr, hw⟩ := fetchIn_some p.segments pc w hf
  obtain ⟨hmem, hdis⟩ := hseg seg hsp
  refine ⟨?_, ?_, ?_⟩
  · show Program.fetchIn P.segments pc = some w
    rw [hw]; exact fetchIn_of_mem P.segments seg hmem hdis pc hr
  · unfold Program.stubAt
    rw [List.find?_eq_none]
    intro st hst
    have := hstub seg hsp st hst
    simp only [decide_eq_true_eq]
    omega
  · have := hexit seg hsp
    omega

/-- a library summary, transferred to a consumer's extracted program -/
theorem lib_summary {p P : Janus.Amd64.Program} (hc : Janus.Contracts.EqHashModel.CodeIn64 p P) {entry : Nat}
    {pre : Janus.Amd64.State → Prop} {post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (h : Janus.Amd64.Tactic.Summary p entry pre post) : Janus.Amd64.Tactic.Summary P entry pre post :=
  Janus.Contracts.EqHashModel.Summary.of_codeIn64 hc h

/-- a library summary, transferred to a consumer's extracted program linked with the runtime-contract implementation `impl`
(`Summary p → (CodeIn64) Summary P → (summary_link) Summary (P.link impl)`) -/
theorem lib_summary_link {p P : Janus.Amd64.Program} (impl : List Janus.Amd64.Segment)
    (hc : Janus.Contracts.EqHashModel.CodeIn64 p P) {entry : Nat}
    {pre : Janus.Amd64.State → Prop} {post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (h : Janus.Amd64.Tactic.Summary p entry pre post) :
    Janus.Amd64.Tactic.Summary (P.link impl) entry pre post :=
  Fv256.B.summary_link impl (lib_summary hc h)

end Fv256.CodeIn
