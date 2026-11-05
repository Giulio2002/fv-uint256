import Janus
import Fv256.Arm64.CodeIn

/-!
# Lifting a library `Reaches` to a consumer's linked program (arm64, Extracted-free)

A run of the library program `lib` (with exit address `ret`) from `st` to a return is a run of `P.link impl`
whenever `lib` is `CodeIn` `P` and `ret` is an admissible return address of `P.link impl`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts.EqHashModel

namespace Fv256.Arm64.DivModBridge

theorem steps_lift {lib P : Program} (hc : CodeIn lib P) (impl : List Segment) (ret : Nat) :
    ∀ {s s' : State} {k : Nat}, Program.Steps (lib.withExit ret) s k s' → Program.Steps (P.link impl) s k s' := by
  intro s s' k h
  induction h with
  | refl => exact .refl _
  | step hx hs hf hst _ ih =>
    obtain ⟨hf', hs', hx'⟩ := hc _ _ hf
    exact .step (by simpa using hx') (by simpa using hs') (Program.fetch_link impl hf') hst ih

theorem run_of_steps {p : Program} {ret : Nat} (hret : RetAddr p ret) :
    ∀ {s : State} {k : Nat} {s' : State}, Program.Steps p s k s' → s'.pc.toNat = ret →
      ∃ fuel, (p.withExit ret).run fuel s = .ok (.returned s') := by
  intro s k s' h
  induction h with
  | refl s =>
    intro hpc
    exact ⟨1, Program.run_succ_exit (p := p.withExit ret) (n := 0) hpc⟩
  | @step s s₁ s₂ k w hx hs hf hst _ ih =>
    intro hpc
    obtain ⟨f, hf'⟩ := ih hpc
    have hne : s.pc.toNat ≠ (p.withExit ret).exitAddr := fun heq => by
      have h2 : s.pc.toNat = ret := heq
      rw [h2, hret.fetch_none] at hf; cases hf
    refine ⟨f + 1, ?_⟩
    rw [Program.run_succ_step (p := p.withExit ret) hne hs hf hst]
    exact hf'

theorem reaches_lift {lib P : Program} (hc : CodeIn lib P) (impl : List Segment) {ret : Nat}
    (hret : RetAddr (P.link impl) ret) {st : State} {Q : State → Prop}
    (h : Reaches (lib.withExit ret) st (IsReturn Q)) : Reaches ((P.link impl).withExit ret) st (IsReturn Q) := by
  obtain ⟨n, o, hr, hq⟩ := h
  cases o with
  | returned s' =>
    obtain ⟨k, hk, hpc⟩ := steps_of_run_returned hr
    obtain ⟨fuel, hrun⟩ := run_of_steps hret (steps_lift hc impl ret hk) hpc
    exact ⟨fuel, .returned s', hrun, hq⟩
  | stub _ _ _ => exact hq.elim

theorem retAddr_lib {lib P : Program} {impl : List Segment} {ret : Nat}
    (hsegs : ∀ seg ∈ lib.segments, seg ∈ P.segments) (hstubs : ∀ st ∈ lib.stubs, st ∈ P.stubs)
    (h : RetAddr (P.link impl) ret) : RetAddr lib ret :=
  ⟨h.aligned, h.user, fun seg hs => h.notCode seg (by simp only [Program.link, List.mem_append]; exact Or.inl (hsegs seg hs)),
    fun st hs => h.notStub st (by simpa using hstubs st hs)⟩

end Fv256.Arm64.DivModBridge
