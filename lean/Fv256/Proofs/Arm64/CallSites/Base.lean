import Janus
import Fv256.Spec.Arm64.CallSites.Base

/-!
# Extracted-free helpers for the arm64 call-site conjuncts (U-WITNESS-CALLSITE)
-/

open Janus Janus.Arm64 Janus.Contracts Janus.Spec

namespace Fv256.Arm64.CallSites

/-- `CallOK` componentwise decidable (all Nat/Bool facts): use `callOK_of` with `by decide` for each part. -/
theorem callOK_of {s : State} {stack nargs : Nat} (h1 : (s.regs 30).toNat % 4 = 0) (h2 : (s.regs 30).toNat < 2 ^ 48)
    (h3 : s.sp.toNat % 16 = 0) (h4 : stack ≤ s.sp.toNat) (h5 : 8 ≤ stack) (h6 : s.sp.toNat + 8 + 8 * nargs ≤ 2 ^ 48)
    (h7 : s.mem.accessible (s.sp.toNat - stack) (stack + 8 + 8 * nargs) true = true) : CallOK s stack nargs :=
  ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem typeOK_of {m : Memory} {t : Nat} (h1 : t + 16 ≤ 2 ^ 48) (h2 : m.accessible t 16 false = true) : TypeOK m t := ⟨h1, h2⟩

theorem guardOK_of {s : State} {adj : Nat} (h1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (h2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true) (h3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + adj < s.sp.toNat) :
    GuardOK s adj := ⟨h1, h2, h3⟩

theorem liveSep_nil (win : List (Nat × Nat)) : LiveSep [] win := fun r hr => absurd hr (by simp)


/-! ### Single-conjunct wrappers of the contracts' preconditions

The auditor matches the contract's whole `pre s_c` against ONE conjunct of the witness (`findConj`), after flattening the witness's
conjunctions; so a multi-part precondition is written through one of these `@[reducible]` defs (reducible: the auditor's first
`isDefEq` is at reducible transparency). Each is the contract's own `pre`, with the contract's arguments. -/

open Janus.Contracts in
theorem strsIn_of {m : Memory} {buf : Nat} {xs : List (Nat × Nat)} (h : ∀ x ∈ xs, StrIn m x.1 x.2) (hb : buf = 0) :
    StrsIn m buf xs := fun x hx => ⟨h x hx, fun hh => absurd hb hh⟩

end Fv256.Arm64.CallSites
