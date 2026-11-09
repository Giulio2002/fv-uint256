import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.IntoBig

/-- The content of the `big.Int` that `*bp` points to in `m`: sign flag clear, a normalized magnitude of at most
four words of capacity at least four, equal to `v`. -/
def BigOut (m : Memory) (bp P v : Nat) : Prop :=
  ∃ ap len cap : Nat, m.readLE bp 8 = P ∧ m.accessible P 32 true = true ∧ P + 32 ≤ 2 ^ 48 ∧
    m.readLE P 1 = 0 ∧ m.readLE (P + 8) 8 = ap ∧ m.readLE (P + 16) 8 = len ∧ m.readLE (P + 24) 8 = cap ∧
    4 ≤ cap ∧ m.accessible ap 32 true = true ∧ ap + 32 ≤ 2 ^ 48 ∧ len ≤ 4 ∧
    (len = 0 ∨ m.readLE (ap + 8 * (len - 1)) 8 ≠ 0) ∧
    Fv256.C.bigAbs (fun i => m.readLE (ap + 8 * i) 8) len = v

/-- The content of the `big.Int` object at `P` alone (without the slot that points to it). -/
def BigObj (m : Memory) (P v : Nat) : Prop :=
  ∃ ap len cap : Nat, m.accessible P 32 true = true ∧ P + 32 ≤ 2 ^ 48 ∧
    m.readLE P 1 = 0 ∧ m.readLE (P + 8) 8 = ap ∧ m.readLE (P + 16) 8 = len ∧ m.readLE (P + 24) 8 = cap ∧
    4 ≤ cap ∧ m.accessible ap 32 true = true ∧ ap + 32 ≤ 2 ^ 48 ∧ len ≤ 4 ∧
    (len = 0 ∨ m.readLE (ap + 8 * (len - 1)) 8 ≠ 0) ∧
    Fv256.C.bigAbs (fun i => m.readLE (ap + 8 * i) 8) len = v

end Fv256.IntoBig
