import Janus

/-!
# Composition glue for `gen_segment` segments (amd64)

A segment lemma has the shape
`seg_k (S) (hpc : S.rip = ofNat pc_k) (hpre : Q_{k-1} S) : ReachesRet P (ofNat pc_{k+1}) S Q_k`
where `Q_k S' := ∃ vs, facts ∧ MemFrame …` is the existential postcondition produced by `tools/gen_segment.py`.
Then `seg_trans (seg_1 S h1 hpre) (fun S' hpc hq => seg_2 S' hpc hq)` is the run through both segments, and so on.
`Q_{k-1}` of the previous segment is literally the `hpre` of the next one (state it as an `abbrev`, or unfold with `obtain`).

This file is shared by FV-F (reduce4) and FV-B (Reciprocal); it has no dependency besides Janus.
-/

open Janus Janus.Amd64 Janus.Amd64.Tactic

namespace Fv256.SegCompose

/-- run through an intermediate address: segment k then segment k+1 -/
theorem seg_trans {p : Janus.Amd64.Program} {ret mid : Janus.Amd64.W64} {S : Janus.Amd64.State} {Q Qmid : Janus.Amd64.State → Prop}
    (h1 : ReachesRet p mid S Qmid)
    (h2 : ∀ S', S'.rip = mid → Qmid S' → ReachesRet p ret S' Q) :
    ReachesRet p ret S Q := by
  obtain ⟨k, s', hs, hr, hq⟩ := h1
  obtain ⟨j, s'', hs2, hr2, hq2⟩ := h2 s' hr hq
  exact ⟨k + j, s'', hs.trans hs2, hr2, hq2⟩

/-- weaken the postcondition of a segment -/
theorem seg_mono {p : Janus.Amd64.Program} {ret : Janus.Amd64.W64} {S : Janus.Amd64.State} {Q Q' : Janus.Amd64.State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ S', Q S' → Q' S') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

/-- a segment run followed by a segment run whose precondition only needs part of the first postcondition (`Q S' → R S'`) -/
theorem seg_trans' {p : Janus.Amd64.Program} {ret mid : Janus.Amd64.W64} {S : Janus.Amd64.State} {Q R T : Janus.Amd64.State → Prop}
    (h1 : ReachesRet p mid S Q) (hQR : ∀ S', Q S' → R S')
    (h2 : ∀ S', S'.rip = mid → R S' → ReachesRet p ret S' T) : ReachesRet p ret S T :=
  seg_trans h1 (fun S' hr hq => h2 S' hr (hQR S' hq))

end Fv256.SegCompose
