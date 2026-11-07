import Janus
import Fv256.Spec

/-!
# `(*uint256.Int).EncodeRLP(w io.Writer) error`: the specification (ISA independent)

Go doc: "EncodeRLP implements the rlp.Encoder interface from go-ethereum and writes the RLP encoding of z to w."
The RLP encoding of an unsigned integer `v` (Ethereum Yellow Paper, Appendix B): `0` is the empty string, `0x80`;
a value below `0x80` is the single byte itself; otherwise `0x80 + n` followed by the `n` bytes of the minimal big-endian
representation (`n = ⌈bitLen v / 8⌉ ≤ 32 < 56`).  A nil receiver encodes as `0` (`0x80`).  Exactly one `w.Write` of
those bytes is made and its error is returned; `*z` is not modified.
-/

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
