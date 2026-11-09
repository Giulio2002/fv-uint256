import Janus

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.IndexByte

/-- the named overread assumption: the 4096-byte pages that contain the `n` bytes at `p` are readable (and below `2^48`) -/
def PageReadable (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  n = 0 ∨ ((p + n - 1) / 4096 * 4096 + 4096 ≤ 2 ^ 48 ∧
    m.accessible (p / 4096 * 4096) ((p + n - 1) / 4096 * 4096 + 4096 - p / 4096 * 4096) false = true)

end Fv256.IndexByte
