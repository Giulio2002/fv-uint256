import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec

/-!
# `(*Int).Scan(src any) error` (amd64): the statement (Extracted-free)

`dst` in `RAX`, the dynamic type word of `src` in `RBX`, the data word in `RCX`.  Plain defs only (the audit rejects consumer
structures).  The three runtime types are `string` (`tyS`), `[]byte` (`tyB`); the dynamic cases are decided by the type word:
`0` (nil), `tyS`, `tyB`, anything else (`unsupported type`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.ScanSpec

namespace Fv256.Amd64.ScanSpec

variable (C : SfdCfg)

/-- the state `s` with the string pair `(p, n)` in `RBX`/`RCX` (so that `TopPre`/`PreU` of `SetFromDecimal` are reused verbatim) -/
def viewS (s : State) (p n : BitVec 64) : State :=
  { s with regs := setRegF (setRegF s.regs 3 p) 1 n }

/-- the string/slice header at the data word: pointer, length -/
def hdrP (s : State) (dw : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (s.mem.readLE dw.toNat 8)
def hdrN (s : State) (dw : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (s.mem.readLE (dw.toNat + 8) 8)

/-- the page-readability the SIMD `IndexByteString` needs for the `[]byte` copy: it lives in the runtime's heap ranges, on the
stack buffer (inside the window) or in the `staticuint64s` table (one-byte strings) -/
def PagesB (R : RtInv) (st lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  Fv256.IndexByte.PageReadable m lo (hi - lo) ∧ (∀ r ∈ R.rt, Fv256.IndexByte.PageReadable m r.1 (r.2 - r.1)) ∧
  Fv256.IndexByte.PageReadable m st 2048

/-- the entry facts of the `[]byte` case: `UnmarshalSpec.PreU` without its hex-path conjunct `okH`, for Scan's frame layout
(the copy buffer is `sp - 40`, `SetFromDecimal` is called from `sp - 72 - 8 ...`).  Only what Scan's code path needs. -/
def PreB (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  (s.regs 0 = z) ∧ (s.regs 3 = pI) ∧ (s.regs 1 = nI) ∧ (Mod C R R2 T L) ∧ (Env C R R2 T b L lo hi s) ∧
  (lo + 4992 ≤ (s.regs 4).toNat) ∧ ((s.regs 4).toNat + 32 ≤ hi) ∧
  (R.ok sb [(s.regs 4).toNat - 40, pI.toNat, nI.toNat]) ∧ (roundupsize nI.toNat true ≤ b) ∧
  (Outside st 2048 [(lo, hi)]) ∧ (Outside st 2048 R.rt) ∧ (Outside st 2048 R2.priv) ∧ (Outside st 2048 [(z.toNat, z.toNat + 32)]) ∧
  (MultOK C z.toNat lo hi s.mem) ∧ (Outside C.mulTab 40 R.rt) ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  (s.mem.accessible C.ioEOF 16 false = true) ∧ (Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧ (Outside C.ioEOF 16 R.rt) ∧
  (s.mem.accessible C.errBig 16 false = true) ∧ (Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧ (Outside C.errBig 16 R.rt) ∧
  (Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) ∧
  (s.mem.accessible C.maxStr 78 false = true) ∧ (Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]) ∧ (Outside C.maxStr 78 R.rt) ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  (Buffer s z 32 true) ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  (Outside z.toNat 32 R2.priv) ∧ (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (Buffer s pI nI.toNat false) ∧ (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

/-- precondition of `Scan`.  `tyS`/`tyB`: the type descriptors of `string`/`[]uint8`, `avx`: the address of `internal/cpu.X86.HasAVX2`
(readability only), `TlsG s`: Go's amd64 TLS convention (`g` at `FS:-8`, reloaded into `R14` after the ABI0 call to `IndexByteString`), `sb`: `runtime.slicebytetostring`, `st`: `runtime.staticuint64s`, `errTy`: the descriptor of `errors.errorString`. -/
def ScanPre (tyS tyB avx sb st errTy : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst tw dw : BitVec 64) (s : State) : Prop :=
  s.regs 0 = dst ∧ s.regs 3 = tw ∧ s.regs 1 = dw ∧ lo + 4992 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 32 ≤ hi ∧
  ((tw = 0 ∧ Buffer s dst 32 true ∧ (dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat) ∧ s.mem.accessible lo (hi - lo) true = true) ∨
   (tw.toNat = tyS ∧ Buffer s dw 16 false ∧ s.mem.accessible avx 1 false = true ∧ TlsG s ∧
      TopPre0 C R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)) ∧
      Fv256.IndexByte.PageReadable s.mem (hdrP s dw).toNat (hdrN s dw).toNat) ∨
   (tw.toNat = tyB ∧ Buffer s dw 24 false ∧ s.mem.accessible avx 1 false = true ∧ TlsG s ∧
      PreB C sb st R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)) ∧
      PagesB R st lo hi s.mem) ∨
   (tw ≠ 0 ∧ tw.toNat ≠ tyS ∧ tw.toNat ≠ tyB ∧ s.mem.accessible (tw.toNat + 16) 4 false = true ∧
      Mod C R R2 T L ∧ Env C R R2 T b L lo hi s ∧ R.ok C.newobject [errTy] ∧ blockSize 16 false ≤ b ∧
      Outside dst.toNat 32 R.rt))

/-- byte `k` of the message `unsupported type` -/
def unsupB (k : Nat) : Nat := ("unsupported type".toList.getD k 'a').toNat

/-- a `*strconv.NumError{ParseUint, chunk, ErrSyntax}` result for the chunk of `n` bytes at `p` in `s` -/
def SynObj (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) (q t : Nat) : Prop :=
  InRanges q (blockSize sl.toNat true) R.rt ∧ InRanges t (blockSize 48 false) R.rt ∧
  ApartAll q (blockSize sl.toNat true) L ∧ ApartAll t (blockSize 48 false) (L ++ [(q, q + blockSize sl.toNat true)]) ∧
  s'.mem.readLE t 8 = fp.toNat ∧ s'.mem.readLE (t + 8) 8 = fl.toNat ∧ s'.mem.readLE (t + 16) 8 = q ∧
  s'.mem.readLE (t + 24) 8 = sl.toNat ∧ s'.mem.readLE (t + 32) 8 = s.mem.readLE C.strconvErrSyntax 8 ∧
  s'.mem.readLE (t + 40) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8 ∧
  (∀ k, k < sl.toNat → s'.mem.readLE (q + k) 1 = s.mem.readLE (sp.toNat + k) 1)

/-- the documented result for the string `(p, n)` -/
def ScanStrPost (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64) (s s' : State) : Prop :=
  ((∃ v, sciParse (bytesAt s.mem p.toNat) n.toNat = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = v) ∨
   (sciParse (bytesAt s.mem p.toNat) n.toNat = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE C.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.ioEOF + 8) 8) ∨
   (sciParse (bytesAt s.mem p.toNat) n.toNat = .range ∧
      (s'.regs 0).toNat = s.mem.readLE C.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.errBig + 8) 8) ∨
   (∃ lo' len', sciParse (bytesAt s.mem p.toNat) n.toNat = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 C.numErrItab ∧ s'.regs 3 = t ∧
        SynObj C R b L (BitVec.ofNat 64 C.fnStr) 9#64 (BitVec.ofNat 64 (p.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat))

/-- precondition of `scanScientificFromString(dst, s)` at its entry (`dst` in `RAX`, `s.ptr` in `RBX`, `s.len` in `RCX`): the
`SetFromDecimal` precondition plus the frame (`0x70` bytes and the return slot below the entry `SP`, so `SetFromDecimal` sees
`lo + 4800 <= SP - 0x78`), the readability of `internal/cpu.X86.HasAVX2` and the pages of the string. -/
def SciPre (avx : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ TopPre0 C R R2 T b L lo hi dst p n s ∧ lo + 4920 ≤ (s.regs 4).toNat ∧ s.mem.accessible avx 1 false = true ∧
  Fv256.IndexByte.PageReadable s.mem p.toNat n.toNat ∧ TlsG s

/-- postcondition of `scanScientificFromString` -/
def SciPost (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧ ScanStrPost C R b L lo hi dst p n s s' ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])

/-- postcondition of `Scan`.  `itab`: the itab `*errors.errorString, error`. -/
def ScanPost (tyS tyB itab : Nat) (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst tw dw : BitVec 64) (s s' : State) : Prop :=
  Kept s s' ∧
  ((tw = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = 0 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (tw.toNat = tyS ∧ ScanStrPost C R b L lo hi dst (hdrP s dw) (hdrN s dw) s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])) ∨
   (tw.toNat = tyB ∧ ScanStrPost C R b L lo hi dst (hdrP s dw) (hdrN s dw) s s' ∧
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])) ∨
   (tw ≠ 0 ∧ tw.toNat ≠ tyS ∧ tw.toNat ≠ tyB ∧ s'.regs 0 = BitVec.ofNat 64 itab ∧
      (∃ (blk ptr : Nat), s'.regs 3 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
        s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧
      Janus.Spec.val256 s'.mem dst.toNat = Janus.Spec.val256 s.mem dst.toNat ∧
      MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])))

end Fv256.Amd64.ScanSpec
