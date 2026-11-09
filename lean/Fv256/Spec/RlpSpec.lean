import Janus
import Fv256.Spec.Core

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus.Arm64

namespace Fv256.Rlp

/-- the RLP encoding of the unsigned integer `v < 2^256` -/
def rlpBytes (v : Nat) : List Nat :=
  if v = 0 then [0x80]
  else if Spec.bitLen v ≤ 7 then [v]
  else (0x80 + (Spec.bitLen v + 7) / 8) :: (List.range ((Spec.bitLen v + 7) / 8)).map
    (fun k => v / 256 ^ ((Spec.bitLen v + 7) / 8 - 1 - k) % 256)

/-- the value `*z` for the receiver pointer `z` (a nil receiver encodes as zero) in memory `m` -/
def rlpVal (m : Memory) (z : Nat) : Nat := if z = 0 then 0 else m.readLE z 32

end Fv256.Rlp
