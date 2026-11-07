import Janus

/-!
# `internal/bytealg.IndexByteString(s string, c byte) int`: the library-summary statement (Extracted-free, both ISAs)

The Go function returns the index of the first byte of `s` equal to `c`, or `-1`.  Nothing here names an extraction or a runtime
variable: a consumer instantiates `IbsSummaryA` / `IbsSummary64` with its own program (`Extracted.program.link impl`) and the code
address of `internal/bytealg.IndexByteString` (arm64) or `IndexByteString.abi0` (amd64) in that program, and takes the summary
as a hypothesis (`hibs`), discharged later by a `CodeIn` transfer from the library program that proves it.

* **Result**: `indexOfNat`: the first `i < n` with `byte i = c % 256`, else `2^64 - 1` (the two's-complement `-1`).
* **amd64** (ABI0, arguments on the stack): at the entry `[RSP]` is the return address, `[RSP+8] = ptr`, `[RSP+16] = len`,
  `[RSP+24] = c` (low byte), the result goes to `[RSP+32]`.  Only that slot is written; `RSP` ends `+8`, `RBP` is kept.  (R14 and X15
  are NOT promised: the caller restores them after the call, as the Go compiler does.)
* **arm64** (register ABI): `X0 = ptr`, `X1 = len`, `X2 = c` (low byte); the result is `X0`; memory is unchanged; `SP`, `X18`, `X28`,
  `X29`, `X30` are kept.

**The one overread assumption** (`PageReadable`): the SIMD code reads whole 16/32-byte blocks around the string and masks the bytes
outside it, so the summary requires the 4096-byte pages that contain the string to be readable.  This is Go's guarantee (a string
never ends in a block next to an unmapped page); 4096 divides every page size of the two targets.
-/

namespace Fv256.IndexByte

/-- the first `i < n` with `b i = c % 256`, else `2^64 - 1` -/
def indexOfNat (b : Nat → Nat) (n c : Nat) : Nat :=
  match (List.range n).find? (fun i => b i == c % 256) with
  | some i => i
  | none => 2 ^ 64 - 1

/-- the bytes of the string at `p` -/
def bytesOf (m : Janus.Arm64.Memory) (p : Nat) : Nat → Nat := fun i => m.readLE (p + i) 1

/-- the named overread assumption: the 4096-byte pages that contain the `n` bytes at `p` are readable (and below `2^48`) -/
def PageReadable (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  n = 0 ∨ ((p + n - 1) / 4096 * 4096 + 4096 ≤ 2 ^ 48 ∧
    m.accessible (p / 4096 * 4096) ((p + n - 1) / 4096 * 4096 + 4096 - p / 4096 * 4096) false = true)

/-! ## amd64 -/

/-- precondition at the entry of `IndexByteString.abi0` (amd64): arguments in `[RSP+8, RSP+32)`, the result slot `[RSP+32, RSP+40)`
writable, the string apart from the result slot.  `avx` is the address of the writable global `internal/cpu.X86.HasAVX2` (the
extractor does not copy it, its value is not fixed): only its READABILITY is assumed, never its value, so the summary holds for both
the SSE2 path (`HasAVX2 = 0`) and the AVX2 path (`HasAVX2 = 1`).  A consumer passes `Extracted.dataAddr.«internal/cpu.X86» + 68`. -/
def IbsPreA (avx : Nat) (p n : BitVec 64) (c : Nat) (s : Janus.Amd64.State) : Prop :=
  s.mem.accessible avx 1 false = true ∧ s.mem.accessible (s.regs 4).toNat 32 false = true ∧
  s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧ (s.regs 4).toNat % 8 = 0 ∧ (s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.readLE ((s.regs 4).toNat + 8) 8 = p.toNat ∧ s.mem.readLE ((s.regs 4).toNat + 16) 8 = n.toNat ∧
  s.mem.readLE ((s.regs 4).toNat + 24) 1 = c % 256 ∧
  s.mem.accessible ((s.regs 4).toNat + 32) 8 true = true ∧
  PageReadable s.mem p.toNat n.toNat ∧ (n.toNat = 0 ∨ p.toNat + n.toNat ≤ (s.regs 4).toNat + 32 ∨ (s.regs 4).toNat + 40 ≤ p.toNat)

/-- postcondition (amd64): the result slot holds the index; `RSP + 8`, `RBP` kept; memory changed only in the result slot -/
def IbsPostA (p n : BitVec 64) (c : Nat) (s s' : Janus.Amd64.State) : Prop :=
  s'.mem.readLE ((s.regs 4).toNat + 32) 8 = indexOfNat (bytesOf s.mem p.toNat) n.toNat c ∧
  s'.regs 4 = s.regs 4 + 8#64 ∧ s'.regs 5 = s.regs 5 ∧
  Janus.MemFrame s.mem s'.mem [((s.regs 4).toNat + 32, (s.regs 4).toNat + 40)]

/-- the summary of `IndexByteString.abi0` on the program `P` (amd64) -/
def IbsSummaryA (P : Janus.Amd64.Program) (entry avx : Nat) (p n : BitVec 64) (c : Nat) : Prop :=
  Janus.Amd64.Tactic.Summary P entry (IbsPreA avx p n c) (IbsPostA p n c)

/-- for every string and byte -/
def IbsLibA (P : Janus.Amd64.Program) (entry avx : Nat) : Prop :=
  ∀ (p n : BitVec 64) (c : Nat), IbsSummaryA P entry avx p n c

/-! ## arm64 -/

/-- precondition at the entry of `IndexByteString` (arm64): `X0 = ptr`, `X1 = len`, `X2 = c`, an admissible link register -/
def IbsPre64 (p n : BitVec 64) (c : Nat) (s : Janus.Arm64.State) : Prop :=
  s.regs 0 = p ∧ s.regs 1 = n ∧ (s.regs 2).toNat % 256 = c % 256 ∧
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧ PageReadable s.mem p.toNat n.toNat

/-- postcondition (arm64): `X0` holds the index; memory, `SP`, `X18`, `X28`, `X29`, `X30` unchanged -/
def IbsPost64 (p n : BitVec 64) (c : Nat) (s s' : Janus.Arm64.State) : Prop :=
  (s'.regs 0).toNat = indexOfNat (bytesOf s.mem p.toNat) n.toNat c ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
  s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30

/-- the summary of `IndexByteString` on the program `P` (arm64) -/
def IbsSummary64 (P : Janus.Program) (entry : Nat) (p n : BitVec 64) (c : Nat) : Prop :=
  Janus.Tactic.Summary P entry (IbsPre64 p n c) (IbsPost64 p n c)

/-- for every string and byte -/
def IbsLib64 (P : Janus.Program) (entry : Nat) : Prop :=
  ∀ (p n : BitVec 64) (c : Nat), IbsSummary64 P entry p n c

end Fv256.IndexByte
