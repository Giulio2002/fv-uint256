import Fv256.ToyRuntime64

/-!
# Toy runtime implementations (amd64), 8-digit strings, for the large-value non-vacuity witnesses

Companions of `Fv256.ToyRuntime64` for an eight-digit string (`z = 10^7`); assembled with `x86_64-linux-gnu-as`.

* `sbts8Code h`: `runtime.slicebytetostring(0, ptr, 8)`: the word at `ptr` stored at the runtime block `h`; returns `(h, 8)`.
* `stb8Code h`: `runtime.stringtoslicebyte(0, ptr, 8)`: the word at `ptr` stored at `h`; returns `(h, 8, 8)`.
* `cat10Code h`: `runtime.concatbyte3(0, q, 1, p, 8, q, 1)`: bytes 8..15 of the block `h` zeroed, then `q[0]`, the eight bytes at `p`, `q[0]`
  stored as ten bytes; returns `(h, 10, 16)`.
-/

namespace Fv256.ToyRuntime64

def sbts8Code (h : Nat) : List Nat :=
  [0x48, 0x8b, 0x13, 0xbf] ++ le32 h ++ [0x48, 0x89, 0x17, 0xb8] ++ le32 h ++ [0xbb, 8, 0, 0, 0, 0xc3]

def stb8Code (h : Nat) : List Nat :=
  [0x48, 0x8b, 0x13, 0xbf] ++ le32 h ++ [0x48, 0x89, 0x17, 0xb8] ++ le32 h ++ [0xbb, 8, 0, 0, 0, 0xb9, 8, 0, 0, 0, 0xc3]

def cat10Code (h : Nat) : List Nat :=
  [0x0f, 0xb6, 0x13, 0x4c, 0x8b, 0x17, 0x45, 0x0f, 0xb6, 0x18, 0xbe] ++ le32 h ++
    [0x48, 0xc7, 0x46, 0x08, 0, 0, 0, 0, 0x88, 0x16, 0x4c, 0x89, 0x56, 0x01, 0x44, 0x88, 0x5e, 0x09, 0xb8] ++ le32 h ++
    [0xbb, 10, 0, 0, 0, 0xb9, 16, 0, 0, 0, 0xc3]

end Fv256.ToyRuntime64
