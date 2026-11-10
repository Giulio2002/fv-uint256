/-!
# Byte encodings shared by the byte-output functions (`Bytes32`, `Bytes20`, `PutUint256`, `WriteToSlice`, ...)

Pure mathematics over `Nat`. `beBytes n x` is the `n`-byte big-endian encoding of the number `x`, and `leBytes n x` the
`n`-byte little-endian one; both keep only the low `n` bytes when `x` does not fit (they spell `x mod 256^n`).
-/

namespace Fv256.Spec

/-- The `n`-byte BIG-endian encoding of `x`, as a list of byte values: element `i` (0 = first = most significant) is
`⌊x / 256^(n-1-i)⌋ mod 256`. When `x ≥ 256^n` the high bytes are dropped, i.e. this encodes `x mod 256^n`.
The natural-number subtraction `n - 1 - i` never truncates, because `i < n` for every `i` in `List.range n`. -/
def beBytes (n x : Nat) : List Nat := (List.range n).map fun i => x / 256 ^ (n - 1 - i) % 256

/-- The `n`-byte LITTLE-endian encoding of `x`: element `i` (0 = first = least significant) is `⌊x / 256^i⌋ mod 256`.
When `x ≥ 256^n` the high bytes are dropped. -/
def leBytes (n x : Nat) : List Nat := (List.range n).map fun i => x / 256 ^ i % 256

/-- Big-endian: most significant byte first. -/
example : beBytes 4 0x01020304 = [1, 2, 3, 4] := by decide

/-- Too short: only the LOW bytes survive. -/
example : beBytes 2 0x010203 = [2, 3] := by decide

/-- Too long: zero padding in front. -/
example : beBytes 3 1 = [0, 0, 1] := by decide

/-- Little-endian: least significant byte first. -/
example : leBytes 4 0x01020304 = [4, 3, 2, 1] := by decide

/-- Both encodings have exactly `n` bytes. -/
theorem beBytes_length (n x : Nat) : (beBytes n x).length = n := by simp [beBytes]

/-- Both encodings have exactly `n` bytes. -/
theorem leBytes_length (n x : Nat) : (leBytes n x).length = n := by simp [leBytes]

end Fv256.Spec
