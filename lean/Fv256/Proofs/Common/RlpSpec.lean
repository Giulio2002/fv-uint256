import Janus
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Legacy.RlpSpec

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

end Fv256.Rlp
