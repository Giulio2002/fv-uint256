import Janus
import Fv256.Proofs.Arm64.CodeIn

/-!
# Moving the library program of `SetFromDecimal` (and its runtime contracts) to the extraction (arm64)

Extracted-free.  `S` is the library program (`SfdProg.program`), `E` the consumer's extraction.  With `ImplApart E impl`
(the one premise on `impl` the auditor allows):
* `codeIn_link_sub`: `E.link impl` has every instruction `S.link impl` has, so summaries of `S.link impl` hold in `E.link impl`;
* `codeIn_ofImpl_sub`: `S.link impl` has every instruction of the runtime's own code `E.ofImpl impl`, so contracts assumed about
  `E.ofImpl impl` hold in `S.link impl`.
-/

open Janus Janus.Contracts Janus.Contracts.EqHashModel

namespace Fv256.Arm64.SfdLink

theorem stubAt_none_of_sub (Q P : Program) (h : ∀ st ∈ Q.stubs, ∃ st' ∈ P.stubs, st'.addr = st.addr) {pc : Nat}
    (hP : P.stubAt pc = none) : Q.stubAt pc = none := by
  unfold Program.stubAt at hP ⊢
  rw [List.find?_eq_none] at hP ⊢
  intro st hst
  obtain ⟨st', h1, h2⟩ := h st hst
  have := hP st' h1
  simp only [decide_eq_true_eq] at this ⊢
  omega

theorem pairwise_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) {l : List α} (hl : l.Pairwise R)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) : R x y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  rw [List.pairwise_iff_getElem] at hl
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact hl i j hi hj h
  · subst h; exact absurd rfl hne
  · exact hs _ _ (hl j i hj hi h)

theorem disj_of_apart {E : Program} {impl : List Segment} (hI : ImplApart E impl) {seg : Segment}
    (hm : seg ∈ E.segments ++ impl) : ∀ seg' ∈ E.segments ++ impl, seg' = seg ∨ Fv256.Arm64.CodeIn.Disj seg seg' := by
  intro seg' hm'
  by_cases h : seg' = seg
  · exact Or.inl h
  · right
    have hs : ∀ a b : Segment, Segment.Apart a b → Segment.Apart b a := fun a b h => by unfold Segment.Apart at h ⊢; omega
    have := pairwise_forall hs hI.1 hm' hm h
    unfold Segment.Apart at this
    unfold Fv256.Arm64.CodeIn.Disj
    omega

theorem codeIn_link_sub (S E : Program) (impl : List Segment)
    (hsub : ∀ seg ∈ S.segments, seg ∈ E.segments)
    (hst : ∀ st ∈ S.stubs, ∃ st' ∈ E.stubs, st'.addr = st.addr)
    (hex : S.exitAddr = E.exitAddr) (hI : ImplApart E impl) :
    CodeIn (S.link impl) (E.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn (S.segments ++ impl) pc = some w := hf
  obtain ⟨seg, hseg, hr1, hr2, hw⟩ := Fv256.Arm64.CodeIn.fetchIn_some _ pc w hf'
  have hm : seg ∈ E.segments ++ impl := by
    rcases List.mem_append.1 hseg with h | h
    · exact List.mem_append_left _ (hsub seg h)
    · exact List.mem_append_right _ h
  have hlen : (pc - seg.base) / 4 < seg.words.length := (List.getElem?_eq_some_iff.1 hw).1
  have hpc : pc = seg.base + 4 * ((pc - seg.base) / 4) := by omega
  obtain ⟨h1, h2⟩ := hI.2 seg hm ((pc - seg.base) / 4) hlen
  rw [← hpc] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · exact Fv256.Arm64.CodeIn.fetchIn_of_mem _ seg hm (disj_of_apart hI hm) pc w ⟨hr1, hr2⟩ hw
  · exact h1
  · show pc ≠ E.exitAddr
    exact h2

theorem codeIn_ofImpl_sub (S E : Program) (impl : List Segment)
    (hst : ∀ st ∈ S.stubs, ∃ st' ∈ E.stubs, st'.addr = st.addr)
    (hex : S.exitAddr = E.exitAddr) (hsub : ∀ seg ∈ S.segments, seg ∈ E.segments)
    (hI : ImplApart E impl) :
    CodeIn (E.ofImpl impl) (S.link impl) := by
  intro pc w hf
  have hf' : Program.fetchIn impl pc = some w := hf
  obtain ⟨seg, hseg, hr1, hr2, hw⟩ := Fv256.Arm64.CodeIn.fetchIn_some _ pc w hf'
  have hm : seg ∈ E.segments ++ impl := List.mem_append_right _ hseg
  have hlen : (pc - seg.base) / 4 < seg.words.length := (List.getElem?_eq_some_iff.1 hw).1
  have hpc : pc = seg.base + 4 * ((pc - seg.base) / 4) := by omega
  obtain ⟨h1, h2⟩ := hI.2 seg hm ((pc - seg.base) / 4) hlen
  rw [← hpc] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · -- no segment of `S` is at `pc`: `S`'s segments are segments of `E`, apart from `impl`
    show Program.fetchIn (S.segments ++ impl) pc = some w
    have hap : ∀ x ∈ S.segments, Segment.Apart x seg := fun x hx =>
      (List.pairwise_append.1 hI.1).2.2 x (hsub x hx) seg hseg
    have hnone : Program.fetchIn S.segments pc = none := by
      cases hh : Program.fetchIn S.segments pc with
      | none => rfl
      | some w' =>
        obtain ⟨x, hx, j, hj, hpcx⟩ := Program.fetchIn_index hh
        have := hap x hx
        unfold Segment.Apart at this
        omega
    rw [fetchIn_append_none impl hnone]; exact hf'
  · show S.stubAt pc = none
    exact stubAt_none_of_sub S E hst h1
  · show pc ≠ S.exitAddr
    rw [hex]; exact h2

end Fv256.Arm64.SfdLink
