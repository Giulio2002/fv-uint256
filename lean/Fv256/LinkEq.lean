import Janus
import Fv256.CodeIn

/-!
# A library program linked with the rest of a consumer's code is the consumer's program

A library program `L` (a few segments, stubs, data, contracts: see `tools/gen_libprog.py`) proves a summary that *assumes* a
runtime contract about the **linked** program `L.link impl'` (`impl'` is a variable).  A consumer extraction `E` contains the
library's segments plus its own (`R` = the segments of `E` that are not in `L`) and is linked with the contract implementation
`impl`.  `progEq_link`: `L.link (R ++ impl)` and `E.link impl` run alike (same fetch, same stubs, same exit address, whatever
`impl` is), so a summary / contract moves between them in both directions (`Summary.of_progEq`, `ProgEq.symm`).
`DataLoaded.of_subset`: the library's data is part of the consumer's.
-/

namespace Fv256.LinkEq

open Janus Janus.Amd64

deriving instance DecidableEq for Janus.Stub
deriving instance DecidableEq for Janus.DataSegment

/-- `p` and `P` run alike: same instruction fetch, same stubs, same exit address. -/
structure ProgEq (p P : Janus.Amd64.Program) : Prop where
  fetch : ∀ pc, p.fetch pc = P.fetch pc
  stub : ∀ pc, p.stubAt pc = P.stubAt pc
  exit : p.exitAddr = P.exitAddr

theorem ProgEq.symm {p P : Janus.Amd64.Program} (h : ProgEq p P) : ProgEq P p :=
  ⟨fun pc => (h.fetch pc).symm, fun pc => (h.stub pc).symm, h.exit.symm⟩

theorem steps_of_progEq {p P : Janus.Amd64.Program} (h : ProgEq p P) {s s' : State} {k : Nat}
    (hst : Janus.Amd64.Program.Steps p s k s') : Janus.Amd64.Program.Steps P s k s' := by
  induction hst with
  | refl => exact .refl _
  | step hx hs hf hstep _ ih =>
    exact .step (by rw [← h.exit]; exact hx) (by rw [← h.stub]; exact hs) (by rw [← h.fetch]; exact hf) hstep ih

theorem Summary.of_progEq {p P : Janus.Amd64.Program} (h : ProgEq p P) {a : Nat} {pre : State → Prop}
    {post : State → State → Prop} (hs : Janus.Amd64.Tactic.Summary p a pre post) :
    Janus.Amd64.Tactic.Summary P a pre post := by
  intro s hpc hpre
  obtain ⟨k, s', hst, hret, hq⟩ := hs s hpc hpre
  exact ⟨k, s', steps_of_progEq h hst, hret, hq⟩

theorem fetchIn_perm (F A : List Janus.Amd64.Segment) (hdis : ∀ s ∈ F, ∀ s' ∈ F, s' = s ∨ Fv256.CodeIn.Disj s s')
    (hFA : ∀ s ∈ F, s ∈ A) (hAF : ∀ s ∈ A, s ∈ F) (pc : Nat) :
    Program.fetchIn F pc = Program.fetchIn A pc := by
  have key : ∀ (F A : List Janus.Amd64.Segment), (∀ s ∈ F, ∀ s' ∈ F, s' = s ∨ Fv256.CodeIn.Disj s s') → (∀ s ∈ F, s ∈ A) →
      (∀ s ∈ A, s ∈ F) → ∀ w, Program.fetchIn F pc = some w → Program.fetchIn A pc = some w := by
    intro F A hdis hFA hAF w hw
    obtain ⟨seg, hseg, hr, rfl⟩ := Fv256.CodeIn.fetchIn_some F pc w hw
    exact Fv256.CodeIn.fetchIn_of_mem A seg (hFA seg hseg) (fun s' hs' => hdis seg hseg s' (hAF s' hs')) pc hr
  cases hF : Program.fetchIn F pc with
  | some w => exact (key F A hdis hFA hAF w hF).symm
  | none =>
    cases hA : Program.fetchIn A pc with
    | none => rfl
    | some w =>
      have := key A F (fun s hs s' hs' => hdis s (hAF s hs) s' (hAF s' hs')) hAF hFA w hA
      rw [hF] at this; cases this

theorem stubAt_perm (l1 l2 : List Janus.Stub) (h12 : ∀ x ∈ l1, x ∈ l2) (h21 : ∀ x ∈ l2, x ∈ l1)
    (hinj : ∀ x ∈ l1, ∀ y ∈ l1, x.addr = y.addr → x = y) (pc : Nat) :
    l1.find? (·.addr = pc) = l2.find? (·.addr = pc) := by
  cases h1 : l1.find? (·.addr = pc) with
  | some x =>
    have hx := List.mem_of_find?_eq_some h1
    have hp := List.find?_some h1
    cases h2 : l2.find? (·.addr = pc) with
    | none =>
      have := List.find?_eq_none.1 h2 x (h12 x hx)
      exact absurd hp this
    | some y =>
      have hy := List.mem_of_find?_eq_some h2
      have hq := List.find?_some h2
      simp only [decide_eq_true_eq] at hp hq
      rw [hinj x hx y (h21 y hy) (by omega)]
  | none =>
    cases h2 : l2.find? (·.addr = pc) with
    | none => rfl
    | some y =>
      have hy := List.mem_of_find?_eq_some h2
      have hq := List.find?_some h2
      have := List.find?_eq_none.1 h1 y (h21 y hy)
      exact absurd hq this

/-- `L` (library) plus the rest `R` of the consumer's segments, linked with `impl`, runs like the consumer `E` linked with `impl`. -/
theorem progEq_link (L E : Janus.Amd64.Program) (R impl : List Janus.Amd64.Segment)
    (hdis : ∀ s ∈ E.segments, ∀ s' ∈ E.segments, s' = s ∨ Fv256.CodeIn.Disj s s')
    (hEA : ∀ s ∈ E.segments, s ∈ L.segments ++ R) (hAE : ∀ s ∈ L.segments ++ R, s ∈ E.segments)
    (hs12 : ∀ x ∈ L.stubs, x ∈ E.stubs) (hs21 : ∀ x ∈ E.stubs, x ∈ L.stubs)
    (hinj : ∀ x ∈ L.stubs, ∀ y ∈ L.stubs, x.addr = y.addr → x = y) (hexit : L.exitAddr = E.exitAddr) :
    ProgEq (L.link (R ++ impl)) (E.link impl) := by
  refine ⟨fun pc => ?_, fun pc => ?_, hexit⟩
  · show Program.fetchIn (L.segments ++ (R ++ impl)) pc = Program.fetchIn (E.segments ++ impl) pc
    rw [← List.append_assoc]
    have hp := fetchIn_perm E.segments (L.segments ++ R) hdis hEA hAE pc
    cases h : Program.fetchIn E.segments pc with
    | some w =>
      rw [h] at hp
      rw [Janus.Amd64.Program.fetchIn_append _ h, Janus.Amd64.Program.fetchIn_append _ hp.symm]
    | none =>
      rw [h] at hp
      rw [Janus.Contracts.EqHashModel.fetchIn_append_none64 _ h, Janus.Contracts.EqHashModel.fetchIn_append_none64 _ hp.symm]
  · show (L.stubs).find? (·.addr = pc) = (E.stubs).find? (·.addr = pc)
    exact stubAt_perm L.stubs E.stubs hs12 hs21 hinj pc
  

/-- Everything needed to use a library program `L`'s summaries inside a consumer's extracted program `E`: `E` has `L`'s
segments, stubs, exit address and data, and its segments are pairwise disjoint. -/
structure LibIn (L E : Janus.Amd64.Program) : Prop where
  dis : ∀ s ∈ E.segments, ∀ s' ∈ E.segments, s' = s ∨ Fv256.CodeIn.Disj s s'
  sub : ∀ s ∈ L.segments, s ∈ E.segments
  stubs12 : ∀ x ∈ L.stubs, x ∈ E.stubs
  stubs21 : ∀ x ∈ E.stubs, x ∈ L.stubs
  inj : ∀ x ∈ L.stubs, ∀ y ∈ L.stubs, x.addr = y.addr → x = y
  exit : L.exitAddr = E.exitAddr
  data : ∀ d ∈ L.data, d ∈ E.data

/-- the segments of the consumer that are not the library's -/
def rest (L E : Janus.Amd64.Program) : List Janus.Amd64.Segment := E.segments.filter (fun s => decide (s ∉ L.segments))

theorem LibIn.progEq {L E : Janus.Amd64.Program} (h : LibIn L E) (impl : List Janus.Amd64.Segment) :
    ProgEq (L.link (rest L E ++ impl)) (E.link impl) := by
  refine progEq_link L E (rest L E) impl h.dis ?_ ?_ h.stubs12 h.stubs21 h.inj h.exit
  · intro s hs
    by_cases hl : s ∈ L.segments
    · exact List.mem_append_left _ hl
    · exact List.mem_append_right _ (List.mem_filter.2 ⟨hs, by simpa using hl⟩)
  · intro s hs
    rcases List.mem_append.1 hs with hl | hr
    · exact h.sub s hl
    · exact (List.mem_filter.1 hr).1

theorem DataLoaded.of_subset {L E : Janus.Amd64.Program} (h : ∀ d ∈ L.data, d ∈ E.data) {m : Janus.Arm64.Memory}
    (hd : E.DataLoaded m) : L.DataLoaded m := fun d hdl => hd d (h d hdl)

end Fv256.LinkEq
