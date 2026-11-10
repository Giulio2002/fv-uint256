import Janus
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.Spec Janus.Contracts Fv256.C

namespace Fv256.Hex

/-- the string at `[p, p+len)` of memory `m` is the hexadecimal rendering of `v` (ISA independent) -/
def HexOut (v : Nat) (m : Memory) (p len : Nat) : Prop :=
  ∃ n, hexDigits v n ∧ StrOut m p len (hexStrBytes v n)

end Fv256.Hex
