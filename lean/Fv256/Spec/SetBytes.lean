/-!
# `SetBytes` and `SetBytes1` ... `SetBytes32`: loading a big-endian byte string into a `uint256.Int`

```go
func (z *Int) SetBytes(buf []byte) *Int      // any length
func (z *Int) SetBytes1(in []byte) *Int      // ... through ...
func (z *Int) SetBytes32(in []byte) *Int     // exactly N bytes (N = 1, 2, ..., 32)
```

All 33 functions do one thing: they read bytes as a big-endian unsigned integer (the first byte is the most significant),
store that number in `z`, and return `z`.

* `z.SetBytes(buf)` uses the LAST `min(len(buf), 32)` bytes of `buf`: a short buffer is used whole (so the empty buffer gives `0`),
  a longer one is cut down to its final 32 bytes. It never panics.
* `z.SetBytesN(in)` (`N = 1 ... 32`) uses the FIRST `N` bytes `in[0:N]` and ignores the rest. If `len(in) < N` it panics
  (a bounds-check failure) and does not touch `z`.

The bytes are modelled as a function `Nat → Nat` giving the byte at each index (every value is below `256`).
-/

namespace Fv256.Spec

/-- THE common definition. `bigEndian b n` is the big-endian number whose digits are the bytes `b 0, b 1, ..., b (n-1)`:
`b 0` is the most significant and `b (n-1)` the least, so `bigEndian b 2 = b 0 * 256 + b 1`. `bigEndian b 0 = 0`. -/
def bigEndian (b : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => b 0 * 256 ^ n + bigEndian (fun i => b (i + 1)) n

/-- How many bytes `z.SetBytes(buf)` takes from a buffer of length `len`: all of them when `len < 32`, otherwise `32`
(that is, `min len 32`). -/
def usedLen (len : Nat) : Nat := if len < 32 then len else 32

/-- Value of `z.SetBytes(buf)` where `buf : Nat → Nat` gives the buffer's bytes and `len` is its length: the big-endian number
formed by the last `min len 32` bytes, namely `buf (len - usedLen len)`, ..., `buf (len - 1)`. -/
def setBytes (buf : Nat → Nat) (len : Nat) : Nat :=
  bigEndian (fun i => buf (len - usedLen len + i)) (usedLen len)

/-- Value of `z.SetBytesN(in)` (for `N = n`, `1 ≤ n ≤ 32`; the call needs `len(in) ≥ n`, else it panics): the big-endian number
formed by the first `n` bytes `in[0], ..., in[n-1]`. Each of `SetBytes1 ... SetBytes32` is this definition at `n = 1 ... 32`. -/
def setBytesN (n : Nat) (buf : Nat → Nat) : Nat := bigEndian buf n

/-- `SetBytes` of an empty buffer is `0`. -/
example : setBytes (fun _ => 0xAB) 0 = 0 := by decide

/-- Bytes read big-endian: `[0x01, 0x02, 0x03]` is `0x010203`. -/
example : setBytes (fun i => [0x01, 0x02, 0x03].getD i 0) 3 = 0x010203 := by decide

/-- A buffer of 33 bytes `[0xFF, 0, ..., 0, 0x01]` keeps only the last 32 bytes, so the leading `0xFF` is dropped. -/
example : setBytes (fun i => if i = 0 then 0xFF else if i = 32 then 0x01 else 0) 33 = 1 := by decide

/-- `SetBytes2` uses exactly the first two bytes and ignores a third. -/
example : setBytesN 2 (fun i => [0x12, 0x34, 0x56].getD i 0) = 0x1234 := by decide

/-- `SetBytes1` is the first byte itself. -/
example : setBytesN 1 (fun i => [0x9C, 0x00].getD i 0) = 0x9C := by decide

/-- `SetBytes32` of a 32-byte buffer ending in `0x01` is `1`. -/
example : setBytesN 32 (fun i => if i = 31 then 0x01 else 0) = 1 := by decide

/-- `SetBytesN` is `SetBytes` restricted to buffers of exactly `N` bytes (`N ≤ 32`): both are the big-endian number of all `N` bytes. -/
theorem setBytesN_eq_setBytes (n : Nat) (h : n ≤ 32) (buf : Nat → Nat) : setBytesN n buf = setBytes buf n := by
  have hu : usedLen n = n := by unfold usedLen; split <;> omega
  simp [setBytesN, setBytes, hu]

end Fv256.Spec
