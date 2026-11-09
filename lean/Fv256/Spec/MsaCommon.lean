import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Spec Janus.Contracts

namespace Fv256.Msa

/-- The cost bound of one `growslice` call made with `newLen ≤ len0 + 32`. -/
def Kc (len0 : Nat) : Nat := 2 * (2 * (len0 + 32) + 192) + 24

/-- The requests the runtime must accept: `m` blocks remain, the next one needs length `n` and the slice has capacity `c`
(a `growslice(p, n, c, 8, uint8)` call is made exactly when `c < n`; its result capacity is `growCap 1 true n c`).
ISA-independent copy of `Fv256.Amd64.Msa.Ready`. -/
def Ready (R : RtInv) (ga u8 : Nat) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | m + 1, n, c => (c < n → (∀ p, R.ok ga [p, n, c, 8, u8]) ∧ Ready R ga u8 m (n + 8) (growCap 1 true n c)) ∧
      (n ≤ c → Ready R ga u8 m (n + 8) c)

/-- **Runtime assumption `DescOK`**: the element type descriptor `u8` (16 bytes: size, pointer bytes) is either
outside the runtime-owned ranges `R.rt`, or described by the runtime invariant (every memory `m` whose runtime view
satisfies `R.inv` has the `uint8` descriptor `(size 1, ptrdata 0)`; its readability comes from `DataLoaded` and the frame).
The real Go runtime satisfies the left disjunct (type descriptors live in read-only data outside the arenas); the generic
toy runtime `toyR tys ok` owns the descriptors of `tys`, and satisfies the right one. It is strictly weaker than
`Outside u8 16 R.rt` alone. Extracted-free so both ISAs share it. -/
def DescOK (R : RtInv) (u8 : Nat) : Prop :=
  Outside u8 16 R.rt ∨
    (∀ b L g m, R.inv b L g (view R.rt L m) → m.readLE u8 8 = 1 ∧ m.readLE (u8 + 8) 8 = 0)

end Fv256.Msa
