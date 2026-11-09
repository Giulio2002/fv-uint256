import Fv256.Spec.BigEndian

/-!
# `func (z *Int) EncodeRLP(w io.Writer) error`

`z.EncodeRLP(w)` writes the RLP encoding of the unsigned integer `z` to the writer `w` with one `w.Write` call and returns that call's
error (it adds none). A nil receiver encodes as zero. The encoding of `x` is:
* `x = 0`: the single byte `0x80` (the empty string);
* `0 < x < 128`: the single byte `x` itself;
* otherwise: the prefix byte `0x80 + n` followed by the `n` bytes of `x` in minimal big-endian form (`n = ⌈bitlen / 8⌉`, no leading zero byte).
-/

namespace Fv256.Spec

/-- The number of bytes in the minimal big-endian encoding of `x` (`0` for `x = 0`); also the length `n` in the RLP prefix. -/
def rlpLen (x : Nat) : Nat := if x = 0 then 0 else x.log2 / 8 + 1

/-- The RLP encoding of the unsigned integer `x < 2^256`, as a list of byte values. -/
def encodeRLP (x : Nat) : List Nat :=
  if x = 0 then [0x80]
  else if x < 128 then [x]
  else (0x80 + rlpLen x) :: beBytes (rlpLen x) x

/-- Zero is the empty string. -/
example : encodeRLP 0 = [0x80] := by decide

/-- A small number is its own encoding. -/
example : encodeRLP 15 = [15] := by decide

/-- `127` is still a single byte, `128` needs a length prefix. -/
example : encodeRLP 127 = [127] ∧ encodeRLP 128 = [0x81, 0x80] := by decide

/-- Two bytes: prefix `0x82`, then the big-endian bytes. -/
example : encodeRLP 0x0400 = [0x82, 4, 0] := by decide

end Fv256.Spec
