import Janus
import Fv256.Spec

namespace Fv256.H
open Janus Janus.Arm64

theorem steps_link {p : Program} (impl : List Segment) {s s' : State} {k : Nat}
    (h : Program.Steps p s k s') : Program.Steps (p.link impl) s k s' := by
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    exact .step (by simpa using hx) (by simpa using hs) (Program.fetch_link impl hf) hst ih

theorem summary_link {p : Program} (impl : List Segment) {entry : Nat}
    {pre : State → Prop} {post : State → State → Prop}
    (h : Janus.Tactic.Summary p entry pre post) : Janus.Tactic.Summary (p.link impl) entry pre post := by
  intro s hpc hp
  obtain ⟨k, s', hst, hr, hq⟩ := h s hpc hp
  exact ⟨k, s', steps_link impl hst, hr, hq⟩

theorem reaches_mono {p : Program} {s : State} {Q Q' : Janus.Outcome → Prop}
    (h : Janus.Tactic.Reaches p s Q) (hq : ∀ o, Q o → Q' o) : Janus.Tactic.Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hq o h2⟩

end Fv256.H
