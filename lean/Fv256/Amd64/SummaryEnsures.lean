import Janus

/-!
# amd64: a `Summary` gives an `Ensures`
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SummaryEnsures

/-- A function `Summary` gives the `Ensures` form, when the summary's postcondition gives the ABI facts. -/
theorem ensures_of_summary64 {p : Janus.Amd64.Program} {entry : Nat} {args : List Janus.Amd64.W64}
    {spre pre : Janus.Amd64.State → Prop} {Q post : Janus.Amd64.State → Janus.Amd64.State → Prop}
    (hsum : Summary p entry spre Q)
    (hpre : ∀ ret s, RetAddr p ret → CallSetup (p.withExit ret) entry args s → pre s → spre s)
    (hpost : ∀ ret s s', RetAddr p ret → CallSetup (p.withExit ret) entry args s → pre s → Q s s' →
      ABIReturn s s' ∧ post s s') :
    Ensures p entry args pre post := by
  intro ret hret s hs hp
  obtain ⟨k, s', hst, hr, hq⟩ := hsum s hs.rip (hpre ret s hret hs hp)
  refine returns_of_steps (Janus.Amd64.Program.Steps.withExit hst hret.fetch_none) ?_
    (hpost ret s s' hret hs hp hq)
  rw [hr, retAddrOf, hs.ret]
  simp only [Janus.Amd64.Program.withExit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hret.user (by decide))

end Fv256.Amd64.SummaryEnsures
