import Extracted
import Fv256.Spec

/-!
# arm64: a `Summary` gives an `Ensures`

The converse of `Janus.Tactic.Ensures.toSummary`: a returning run of the extracted program `p` that ends at
an admissible return address `ret` is a returning run of `p.withExit ret`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic

namespace Fv256.Arm64.SummaryEnsures

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

theorem ensures_of_summary {p : Program} {entry : Nat} {args : List W64} {pre : State → Prop}
    {post : State → State → Prop} (PRE : State → Prop) (POST : State → State → Prop)
    (h : Summary p entry pre post)
    (hpre : ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → PRE s → pre s)
    (hpost : ∀ ret, RetAddr p ret → ∀ s, CallSetup (p.withExit ret) entry args s → PRE s →
      ∀ s', post s s' → ABIReturn s s' ∧ POST s s') :
    Ensures p entry args PRE POST := by
  intro ret hret s hsu hP
  have hs := h s hsu.pc (hpre ret hret s hsu hP)
  rw [hsu.lr] at hs
  obtain ⟨k, s', hk, hpc, hq⟩ := hs
  have hpc' : s'.pc.toNat = ret := by
    have := congrArg BitVec.toNat hpc
    simp only [Program.withExit, BitVec.toNat_ofNat] at this
    rw [this]; exact Nat.mod_eq_of_lt (by have := hret.user; omega)
  obtain ⟨fuel, hr⟩ := run_of_steps hret hk hpc'
  exact ⟨fuel, s', hr, hpost ret hret s hsu hP s' hq⟩

end Fv256.Arm64.SummaryEnsures
