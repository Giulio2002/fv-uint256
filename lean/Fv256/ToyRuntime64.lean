import Janus

/-!
# Toy runtime implementations (amd64) for non-vacuity witnesses

Machine code for small implementations of runtime functions, linked at the contract address of a consumer's witness
(`Extracted.program.link [⟨"model", addr, code⟩]`).  A witness proves `RtContract64 (… .link impl) addr rt 4096 H spec` for
its toy once per consumer (`janus64_run`, then `rtPost_const` or `RtPost64.intro`), with a readiness `H` that the
consumer's hypotheses also use.

* `sbtsIdCode`: `runtime.slicebytetostring(buf, ptr, n)` returning the argument string itself (`MOV RAX,RBX; MOV RBX,RCX; RET`).
  It meets `slicebytetostringSpec` for every call (memory unchanged; the spec only promises the bytes and readability), so the
  readiness can be `fun _ _ _ _ => True`.  Used by `Fv256.Amd64.Dec.Witness`.  It returns a pointer INTO the caller's own
  string, so it does not satisfy a hypothesis that the result lies outside the caller's stack window.
* `stb1Code h`: `runtime.stringtoslicebyte(0, ptr, 1)` for a one-byte string: copies the byte to the heap word `h`
  (zero-extended to 8 bytes: len 1, cap 8 = `roundupsize 1`) and returns `(h, 1, 8)`.
* `convTstringCode h`: `runtime.convTstring(ptr, len)`: stores the 16-byte header `(ptr, len)` at `h`, returns `h`.
* `cat3OnesCode h`: `runtime.concatbyte3(0, a, 1, b, 1, c, 1)` for three one-byte strings: the three bytes zero-extended
  into the heap word `h`, returns `(h, 3, 8)`.

The last three are not yet used by a proof (MarshalText / Value / MarshalJSON wait on the String issue).
-/

namespace Fv256.ToyRuntime64

def le32 (c : Nat) : List Nat := [c % 256, c / 256 % 256, c / 65536 % 256, c / 16777216 % 256]

def sbtsIdCode : List Nat := [0x48, 0x89, 0xd8, 0x48, 0x89, 0xcb, 0xc3]

def stb1Code (h : Nat) : List Nat :=
  [0x0f, 0xb6, 0x03] ++ [0xbf] ++ le32 h ++ [0x48, 0x89, 0x07] ++ [0xb8] ++ le32 h ++ [0xbb, 1, 0, 0, 0] ++ [0xb9, 8, 0, 0, 0] ++ [0xc3]

def convTstringCode (h : Nat) : List Nat :=
  [0xbf] ++ le32 h ++ [0x48, 0x89, 0x07, 0x48, 0x89, 0x5f, 0x08, 0xb8] ++ le32 h ++ [0xc3]

def cat3OnesCode (h : Nat) : List Nat :=
  [0x0f, 0xb6, 0x03, 0x0f, 0xb6, 0x17, 0xc1, 0xe2, 0x08, 0x09, 0xd0, 0x41, 0x0f, 0xb6, 0x10, 0xc1, 0xe2, 0x10, 0x09, 0xd0] ++
  [0xbf] ++ le32 h ++ [0x48, 0x89, 0x07, 0xb8] ++ le32 h ++ [0xbb, 3, 0, 0, 0, 0xb9, 8, 0, 0, 0, 0xc3]

/-- `runtime.slicebytetostring(0, ptr, n)` copying into the runtime block at `h` (any length `n`, no `CLD` needed: a byte loop):
```
mov edi,h ; xor edx,edx ; L: cmp rdx,rcx ; jae D ; movzx esi,[rbx+rdx] ; mov [rdi+rdx],sil ; inc rdx ; jmp L
D: mov rbx,rcx ; mov eax,h ; ret
```
It clobbers `RSI, RDX, RDI`; returns `(h, n)`.  The block `[h, h+n)` must be runtime-owned and writable and apart from `[ptr, ptr+n)`
(the witness's readiness states it). -/
def sbtsCopyCode (h : Nat) : List Nat :=
  [0xbf] ++ le32 h ++ [0x31, 0xd2, 0x48, 0x39, 0xca, 0x73, 0x0d, 0x0f, 0xb6, 0x34, 0x13, 0x40, 0x88, 0x34, 0x17,
    0x48, 0xff, 0xc2, 0xeb, 0xee, 0x48, 0x89, 0xcb, 0xb8] ++ le32 h ++ [0xc3]

theorem sbtsCopyCode_length (h : Nat) : (sbtsCopyCode h).length = 34 := by simp [sbtsCopyCode, le32]

theorem stb1Code_length (h : Nat) : (stb1Code h).length = 27 := by simp [stb1Code, le32]

end Fv256.ToyRuntime64
