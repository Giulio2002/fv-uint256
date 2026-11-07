import Janus

/-!
# Toy runtime implementations (arm64), 8-byte strings, for the large-value non-vacuity witnesses

Instruction words (assembled with `aarch64-linux-gnu-as`), linked at the contract address of a consumer's witness; companions of
`Fv256.ToyRuntimeArm64` for an 8-digit string (`z = 10^7`).

* `sbts8Words`: `runtime.slicebytetostring(0, ptr, 8)`: the word at `ptr` stored at the runtime block `0x600000`; returns `(0x600000, 8)`.
* `stb8Words`: `runtime.stringtoslicebyte(0, ptr, 8)`: the word at `ptr` stored at `0x610000`; returns `(0x610000, 8, 8)`.
-/

namespace Fv256.ToyRuntimeArm64

def sbts8Words : List Nat :=
  [0xf9400023, 0xd2a00c05, 0xf90000a3, 0xaa0503e0, 0xd2800101, 0xd65f03c0]

def stb8Words : List Nat :=
  [0xf9400023, 0xd2a00c25, 0xf90000a3, 0xaa0503e0, 0xd2800101, 0xd2800102, 0xd65f03c0]

end Fv256.ToyRuntimeArm64
