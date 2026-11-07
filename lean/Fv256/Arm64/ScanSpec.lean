import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SpecScan
import Fv256.IndexByteSpec
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.ScanSciSpec

/-!
# `(*Int).Scan(src any) error` (arm64): the statement (Extracted-free)

`dst` in `X0`, the dynamic type word of `src` in `X1`, the data word in `X2`.  Plain defs only (the audit rejects consumer
structures).  The dynamic cases are decided by the type word: `0` (nil), `tyS` (`string`), `tyB` (`[]uint8`), anything else
(`unsupported type`).  Mirrors `Fv256.Amd64.ScanSpec`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.ScanSpec

namespace Fv256.Arm64.ScanSpec

variable (C : SfdCfg)

/-- the state `s` with the string pair `(p, n)` in `X1`/`X2` (so that `TopPre0` is stated as for `SetFromDecimal`) -/
def viewS (s : State) (p n : BitVec 64) : State :=
  { s with regs := setReg (setReg s.regs 1 p) 2 n }

/-- the string/slice header at the data word: pointer, length -/
def hdrP (s : State) (dw : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (s.mem.readLE dw.toNat 8)
def hdrN (s : State) (dw : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (s.mem.readLE (dw.toNat + 8) 8)

/-- `SfdTopSpec.TopPre` without the two facts about the caller's return address (`X30`), which the call establishes -/
def TopPre0 (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  s.regs 0 = z ∧ s.regs 1 = pS ∧ s.regs 2 = nS ∧ Mod C R R2 T L ∧
  Env C R R2 T b L lo hi s ∧ lo + 4528 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ hi ∧
  MultOK C z.toNat lo hi s.mem ∧
  s.mem.accessible C.ioEOF 16 false = true ∧ Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  s.mem.accessible C.maxStr 78 false = true ∧ Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside C.maxStr 78 R.rt ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  s.mem.accessible C.errBig 16 false = true ∧ Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  Ptr32 s.mem z true ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  Outside z.toNat 32 R2.priv ∧ (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16) ∧
  (nS.toNat = 0 ∨ s.mem.accessible pS.toNat nS.toNat false = true) ∧ pS.toNat + nS.toNat ≤ 2 ^ 48 ∧
  (nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat) ∧
  ChunkAll C R R2 L b pS.toNat nS.toNat lo hi s.mem

theorem TopPre0.toTop {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS nS : BitVec 64}
    {s : State} (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 48)
    (h : TopPre0 C R R2 T b L lo hi z pS nS s) : TopPre C R R2 T b L lo hi z pS nS s := by
  unfold TopPre0 at h; unfold TopPre; exact ⟨h30a, h30b, h⟩

/-- the page-readability the SIMD `IndexByteString` needs for the `[]byte` copy: it lives in the runtime's heap ranges, on the
stack buffer (inside the window) or in the `staticuint64s` table (one-byte strings) -/
def PagesB (R : RtInv) (st lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  Fv256.IndexByte.PageReadable m lo (hi - lo) ∧ (∀ r ∈ R.rt, Fv256.IndexByte.PageReadable m r.1 (r.2 - r.1)) ∧
  Fv256.IndexByte.PageReadable m st 2048

/-- the entry facts of the `[]byte` case: what `TopPre0` for the copy `string(b)` needs, stated before the copy exists
(`Scan`'s frame is 80 bytes, the copy buffer is `sp - 40`).  Only what Scan's code path needs. -/
def PreB (sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pI nI : BitVec 64) (s : State) : Prop :=
  Mod C R R2 T L ∧ Env C R R2 T b L lo hi s ∧
  R.ok sb [s.sp.toNat - 40, pI.toNat, nI.toNat] ∧ roundupsize nI.toNat true ≤ b ∧
  Outside st 2048 [(lo, hi)] ∧ Outside st 2048 R.rt ∧ Outside st 2048 R2.priv ∧ Outside st 2048 [(z.toNat, z.toNat + 32)] ∧
  MultOK C z.toNat lo hi s.mem ∧ Outside C.mulTab 40 R.rt ∧
  (∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt) ∧
  s.mem.accessible C.ioEOF 16 false = true ∧ Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside C.ioEOF 16 R.rt ∧
  s.mem.accessible C.errBig 16 false = true ∧ Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside C.errBig 16 R.rt ∧
  InitDone C R2 s.mem ∧
  s.mem.accessible C.maxStr 78 false = true ∧ Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)] ∧ Outside C.maxStr 78 R.rt ∧
  (∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k) ∧
  Ptr32 s.mem z true ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  Outside z.toNat 32 R2.priv ∧ (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16) ∧
  Ptr s.mem pI nI.toNat false ∧ (pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat) ∧
  (∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true) ∧
  (∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧
    blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true)

/-- precondition of `Scan`.  `tyS`/`tyB`: the type descriptors of `string`/`[]uint8`, `sb`: `runtime.slicebytetostring`,
`st`: `runtime.staticuint64s`, `errTy`: the descriptor of `errors.errorString`.  The common part is the call state: `Scan`'s
80-byte frame and `scanScientificFromString`'s below it fit the window, the stack-growth prologue falls through. -/
def ScanPre (tyS tyB sb st errTy : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst tw dw : BitVec 64) (s : State) : Prop :=
  s.regs 0 = dst ∧ s.regs 1 = tw ∧ s.regs 2 = dw ∧ lo + 4720 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ hi ∧ hi ≤ 2 ^ 48 ∧
  s.sp.toNat % 16 = 0 ∧ GuardOK s 80 ∧
  ((tw = 0 ∧ Ptr s.mem dst 32 true ∧ (dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat) ∧ s.mem.accessible lo (hi - lo) true = true) ∨
   (tw.toNat = tyS ∧ Ptr s.mem dw 16 false ∧ (dw.toNat + 16 ≤ lo ∨ hi ≤ dw.toNat) ∧
      TopPre0 C R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)) ∧
      InitDone C R2 s.mem ∧ Fv256.IndexByte.PageReadable s.mem (hdrP s dw).toNat (hdrN s dw).toNat) ∨
   (tw.toNat = tyB ∧ Ptr s.mem dw 24 false ∧ (dw.toNat + 24 ≤ lo ∨ hi ≤ dw.toNat) ∧
      PreB C sb st R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s ∧ PagesB R st lo hi s.mem) ∨
   (tw ≠ 0 ∧ tw.toNat ≠ tyS ∧ tw.toNat ≠ tyB ∧ s.mem.accessible (tw.toNat + 16) 4 false = true ∧
      (tw.toNat + 16 + 4 ≤ lo ∨ hi ≤ tw.toNat + 16) ∧ Mod C R R2 T L ∧ Env C R R2 T b L lo hi s ∧ R.ok C.newobject [errTy] ∧ blockSize 16 false ≤ b ∧
      Outside dst.toNat 32 R.rt ∧ (dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat) ∧
      (∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)))

/-- byte `k` of the message `unsupported type` -/
def unsupB (k : Nat) : Nat := ("unsupported type".toList.getD k 'a').toNat

/-- a `*strconv.NumError{ParseUint, chunk, ErrSyntax}` result for the chunk of `n` bytes at `sp` in `s` -/
def SynObj (R : RtInv) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) (q t : Nat) : Prop :=
  InRanges q (blockSize sl.toNat true) R.rt ∧ InRanges t (blockSize 48 false) R.rt ∧
  ApartAll q (blockSize sl.toNat true) L ∧ ApartAll t (blockSize 48 false) (L ++ [(q, q + blockSize sl.toNat true)]) ∧
  s'.mem.readLE t 8 = fp.toNat ∧ s'.mem.readLE (t + 8) 8 = fl.toNat ∧ s'.mem.readLE (t + 16) 8 = q ∧
  s'.mem.readLE (t + 24) 8 = sl.toNat ∧ s'.mem.readLE (t + 32) 8 = s.mem.readLE C.strconvErrSyntax 8 ∧
  s'.mem.readLE (t + 40) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8 ∧
  (∀ k, k < sl.toNat → s'.mem.readLE (q + k) 1 = s.mem.readLE (sp.toNat + k) 1)

/-- the documented result for the string `(p, n)` -/
def ScanStrPost (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64)
    (s s' : State) : Prop :=
  ((∃ v, sciParse (bytesAt s.mem p.toNat) n.toNat = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = v ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (sciParse (bytesAt s.mem p.toNat) n.toNat = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE C.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (C.ioEOF + 8) 8 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (sciParse (bytesAt s.mem p.toNat) n.toNat = .range ∧
      (s'.regs 0).toNat = s.mem.readLE C.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (C.errBig + 8) 8 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (∃ lo' len', sciParse (bytesAt s.mem p.toNat) n.toNat = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 C.numErrItab ∧ s'.regs 1 = t ∧
        SynObj C R L (BitVec.ofNat 64 C.fnStr) 9#64 (BitVec.ofNat 64 (p.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])))

/-- the registers a return keeps -/
def Kept (s s' : State) : Prop := s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18

/-- postcondition of `Scan`.  `itab`: the itab `*errors.errorString, error`. -/
def ScanPost (tyS tyB itab : Nat) (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (dst tw dw : BitVec 64) (s s' : State) : Prop :=
  Kept s s' ∧
  ((tw = 0 ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = 0 ∧
      MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]) ∨
   (tw.toNat = tyS ∧ ScanStrPost C R R2 L lo hi dst (hdrP s dw) (hdrN s dw) s s') ∨
   (tw.toNat = tyB ∧ ScanStrPost C R R2 L lo hi dst (hdrP s dw) (hdrN s dw) s s') ∨
   (tw ≠ 0 ∧ tw.toNat ≠ tyS ∧ tw.toNat ≠ tyB ∧ s'.regs 0 = BitVec.ofNat 64 itab ∧
      (∃ (blk ptr : Nat), s'.regs 1 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
        s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧
      Janus.Spec.val256 s'.mem dst.toNat = Janus.Spec.val256 s.mem dst.toNat ∧
      MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])))

end Fv256.Arm64.ScanSpec
