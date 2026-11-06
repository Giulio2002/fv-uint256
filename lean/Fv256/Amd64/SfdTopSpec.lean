import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.HexLemmas

/-!
# `(*Int).SetFromDecimal(s string) error` (amd64): the statement (Extracted-free)

Nothing here names an extraction.  Every binary-specific address (package variables, runtime type descriptors, runtime
entry points) is a field of `SfdCfg`; a consumer instantiates it for its own binary (the proof instantiates it with the
`Extracted.dataAddr` / `contractAddr` values).  `TopPre`/`TopPost` are the Pre/Post of `Summary P entry (TopPre ..) (TopPost ..)`:
`z` in `RAX`, `s.ptr` in `RBX`, `s.len` in `RCX`; the `error` result is `RAX` (itab or type word) and `RBX` (data word), nil = `0, 0`.

The result is by cases on `Fv256.I.decParse` (the documented behaviour): the number (`ok v`: `z = v`, `err = nil`), `io.EOF`
(no digits left: `z = 0`), `ErrBig256Range` (too large: `z` unchanged), or the `*strconv.NumError{ParseUint, chunk, ErrSyntax}`
for the failing 19-digit chunk (`TeObj`, `z = 0`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I

namespace Fv256.Amd64.SfdTopSpec

/-- the binary-specific addresses -/
structure SfdCfg where
  ioEOF : Nat            -- package variable `io.EOF` (an `error` interface value: 2 words)
  errBig : Nat           -- package variable `uint256.ErrBig256Range`
  mulTab : Nat           -- package variable `uint256.multipliers` (`[5]*Int`)
  numErrType : Nat       -- type descriptor `strconv.NumError`
  numErrItab : Nat       -- itab `*strconv.NumError, error`
  errItab : Nat          -- itab `internal/strconv.Error, error`
  synConst : Nat         -- constant `internal/strconv.ErrSyntax` object
  strconvErrSyntax : Nat -- package variable `strconv.ErrSyntax`
  wbFlag : Nat           -- `runtime.writeBarrier`
  fnStr : Nat            -- the string constant "ParseUint"
  mallocgc : Nat         -- entry of `runtime.mallocgc`
  memmove : Nat
  newobject : Nat
  wb1 : Nat              -- `runtime.gcWriteBarrier1`
  wb2 : Nat

variable (C : SfdCfg)

/-- the ranges the static facts read (the descriptor `T` has 48 bytes). -/
def staticRanges (T : Nat) : List (Nat × Nat) :=
  [(C.errItab, C.errItab + 16), (C.synConst, C.synConst + 8), (C.strconvErrSyntax, C.strconvErrSyntax + 16),
    (C.wbFlag, C.wbFlag + 4), (C.numErrType, C.numErrType + 16), (T, T + 48)]

def StaticOK (R2 : IfaceModel) (T : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE (C.errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory m T = true ∧ isDirectIface m T = false ∧
  tySize m T = 8 ∧ m.readLE C.numErrType 8 = 48 ∧ m.readLE (C.numErrType + 8) 8 ≠ 0 ∧
  m.accessible C.wbFlag 4 false = true ∧ m.accessible C.strconvErrSyntax 16 false = true ∧
  m.accessible C.errItab 16 false = true ∧ m.accessible C.synConst 8 false = true ∧ m.accessible C.numErrType 16 false = true

/-- the runtime environment for the absolute stack window `[lo, hi)` -/
def Env (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (s : State) : Prop :=
  lo ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 ≤ hi ∧ hi ≤ 2 ^ 48 ∧ (s.regs 4).toNat % 8 = 0 ∧
  s.mem.accessible lo (hi - lo) true = true ∧
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 14).toNat + 16) 8 < lo ∧
  Outside lo (hi - lo) R.rt ∧ Outside lo (hi - lo) R2.priv ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R2.priv ∧
  ((s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 14).toNat + 16) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(lo, hi)]) ∧
  StaticOK C R2 T s.mem ∧ R2.Env s.mem (s.regs 14) ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(lo, hi)])

/-- the state-independent runtime-model facts -/
def Mod (R : RtInv) (R2 : IfaceModel) (T : Nat) (L : List (Nat × Nat)) : Prop :=
  R2.Laws ∧ R2.depth ≤ 4096 ∧ R2.IsType T ∧ (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧ (∀ r ∈ R.rt, 0 < r.1) ∧
  (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R2.priv) ∧
  R.ok C.newobject [C.numErrType] ∧ R.ok C.wb1 [1] ∧ R.ok C.wb2 [2]

/-- the facts about a 1..19-byte chunk `(sp, sl)` that `strconv.ParseUint` may copy for its error value -/
def ChunkOK (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (sp sl : BitVec 64) (lo hi : Nat)
    (m : Janus.Arm64.Memory) : Prop :=
  R.ok C.mallocgc [sl.toNat, 0, 0] ∧ (∀ q, R.ok C.memmove [q, sp.toNat, sl.toNat]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  m.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ lo ∨ hi ≤ sp.toNat) ∧
  (Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L) ∧ Outside sp.toNat sl.toNat R2.priv

/-- every 1..19-byte chunk of the string `(pS, nS)` meets `ChunkOK` -/
def ChunkAll (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (pS nS lo hi : Nat)
    (m : Janus.Arm64.Memory) : Prop :=
  ∀ sp sl : Nat, pS ≤ sp → sp + sl ≤ pS + nS → 1 ≤ sl → sl ≤ 19 →
    ChunkOK C R R2 L b (BitVec.ofNat 64 sp) (BitVec.ofNat 64 sl) lo hi m

/-- the package variable `multipliers` as memory holds it -/
def MultOK (z lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.accessible C.mulTab 40 false = true ∧ Outside C.mulTab 40 [(lo, hi), (z, z + 32)] ∧
  ∀ k, 1 ≤ k → k ≤ 4 →
    m.accessible (m.readLE (C.mulTab + 8 * k) 8) 32 false = true ∧ m.readLE (C.mulTab + 8 * k) 8 + 32 ≤ 2 ^ 48 ∧
    Janus.Spec.val256 m (m.readLE (C.mulTab + 8 * k) 8) = 10 ^ (19 * k) ∧
    Outside (m.readLE (C.mulTab + 8 * k) 8) 32 [(lo, hi), (z, z + 32)]

/-- the fresh `*strconv.NumError` object `t` and copy `q` of the chunk (as `strconv.toError` builds them) -/
def TeObj (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) (q t : Nat) : Prop :=
  InRanges q (blockSize sl.toNat true) R.rt ∧ InRanges t (blockSize 48 false) R.rt ∧
  ApartAll q (blockSize sl.toNat true) L ∧ ApartAll t (blockSize 48 false) (L ++ [(q, q + blockSize sl.toNat true)]) ∧
  s'.mem.readLE t 8 = fp.toNat ∧ s'.mem.readLE (t + 8) 8 = fl.toNat ∧ s'.mem.readLE (t + 16) 8 = q ∧
  s'.mem.readLE (t + 24) 8 = sl.toNat ∧ s'.mem.readLE (t + 32) 8 = s.mem.readLE C.strconvErrSyntax 8 ∧
  s'.mem.readLE (t + 40) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8 ∧
  (∀ k, k < sl.toNat → s'.mem.readLE (q + k) 1 = s.mem.readLE (sp.toNat + k) 1) ∧
  R.inv (b - blockSize sl.toNat true - blockSize 48 false)
    (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) (s.regs 14).toNat
    (view R.rt (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) s'.mem)

open Fv256.C in
/-- Precondition of `SetFromDecimal(z, s)`: `z` in `RAX`, `s.ptr` in `RBX`, `s.len` in `RCX`; `[lo, hi)` is the stack window
the call (and everything it calls) may use. -/
def TopPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = pS ∧ s.regs 1 = nS ∧ Mod C R R2 T L ∧
  Env C R R2 T b L lo hi s ∧ lo + 4800 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 32 ≤ hi ∧
  MultOK C z.toNat lo hi s.mem ∧
  s.mem.accessible C.ioEOF 16 false = true ∧ Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  s.mem.accessible C.errBig 16 false = true ∧ Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  Buffer s z 32 true ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  Outside z.toNat 32 R2.priv ∧ (∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  Buffer s pS nS.toNat false ∧ (pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat) ∧
  ChunkAll C R R2 L b pS.toNat nS.toNat lo hi s.mem

open Fv256.C in
/-- Postcondition: the documented result `decParse` of the string's bytes. -/
def TopPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧
  ((∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v ∧ Env C R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE C.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0 ∧ Env C R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
      (s'.regs 0).toNat = s.mem.readLE C.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (C.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat ∧ Env C R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (∃ lo' len', decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 C.numErrItab ∧ s'.regs 3 = t ∧
        TeObj C R b L (BitVec.ofNat 64 C.fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])))

/-- the statement of the summary of `SetFromDecimal` on a program `P` with entry `entry` -/
def SfdSummary (P : Janus.Amd64.Program) (entry : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) : Prop :=
  Summary P entry (TopPre C R R2 T b L lo hi z pS nS) (TopPost C R R2 T b L lo hi z pS nS)

end Fv256.Amd64.SfdTopSpec
