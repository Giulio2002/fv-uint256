import Janus

/-!
# Toy runtime implementations (arm64) for non-vacuity witnesses

Instruction words (assembled with `aarch64-linux-gnu-as`) of small implementations of runtime functions, linked at the contract
address of a consumer's witness (`Extracted.program.link [⟨"model", addr, words⟩]`); the arm64 counterparts of `ToyRuntime64`.

* `sbts2Words`: `runtime.slicebytetostring(0, ptr, 2)`: both bytes read, then stored at the runtime block `0x600000`; returns `(0x600000, 2)`.
* `stb2Words`: `runtime.stringtoslicebyte(0, ptr, 2)`: the two bytes stored (zero-extended to 8 bytes) at `0x610000`; returns `(0x610000, 2, 8)`.
-/

namespace Fv256.ToyRuntimeArm64

def sbts2Words : List Nat :=
  [0x39400023, 0x39400424, 0xd2a00c05, 0x390000a3, 0x390004a4, 0xaa0503e0, 0xd2800041, 0xd65f03c0]

def stb2Words : List Nat :=
  [0x39400023, 0x39400424, 0xaa042063, 0xd2a00c25, 0xf90000a3, 0xaa0503e0, 0xd2800041, 0xd2800102, 0xd65f03c0]

end Fv256.ToyRuntimeArm64
