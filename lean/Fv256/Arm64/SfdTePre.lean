import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdProg
import Fv256.Arm64.SfdEnv

/-!
# `strconv.toError(fn, s, base, bitSize, err)` for `err == ErrSyntax` (arm64): statements

Registers: `fn = (X0, X1)`, `s = (X2, X3)`, `base = X4`, `bitSize = X5`, `err = (X6, X7)`.
For `err = strconv.ErrSyntax` (`X6 = errItab`, `X7 = synConst`) the result is
`&NumError{Func: fn, Num: cloneString(s), Err: strconv.ErrSyntax}`: `X0 = numErrItab`, `X1 = t`.
`TeObj` is the same fact list as on amd64 (the shared spec of `ParseUint`'s syntax error).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Arm64.SfdEnv

namespace Fv256.Arm64.SfdToError

abbrev te : Nat := segAddr Fv256.Arm64.SfdProg.program "strconv.toError"
abbrev P : Program := Fv256.Arm64.SfdProg.program

/-- the state-independent model facts -/
def Mod (R : RtInv) (R2 : IfaceModel) (T : Nat) (L : List (Nat × Nat)) : Prop :=
  R2.Laws ∧ 8 ≤ R2.depth ∧ R2.depth ≤ 4096 ∧ R2.IsType T ∧ (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧ (∀ r ∈ R.rt, 0 < r.1) ∧
  (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ staticRanges T, r ≠ (T, T + 48) → Outside r.1 (r.2 - r.1) R2.priv) ∧
  R.ok (P.contractAddr "runtime.newobject") [numErrType] ∧
  R.ok (P.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (P.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  (∀ (m : Janus.Arm64.Memory) (g : BitVec 64), R2.Env m g →
    isRegularMemory m T = true ∧ isDirectIface m T = false ∧ tySize m T = 8)

/-- the facts about the string `(sp, sl)` being copied -/
def ChunkOK (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (sp sl : BitVec 64) (lo hi : Nat)
    (m : Janus.Arm64.Memory) : Prop :=
  R.ok (P.contractAddr "runtime.mallocgc") [sl.toNat, 0, 0] ∧
  (∀ q, R.ok (P.contractAddr "runtime.memmove") [q, sp.toNat, sl.toNat]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  m.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ lo ∨ hi ≤ sp.toNat) ∧
  (Outside sp.toNat sl.toNat R.rt ∨ InRanges sp.toNat sl.toNat L) ∧ Outside sp.toNat sl.toNat R2.priv

def TePre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
  s.regs 0 = fp ∧ s.regs 1 = fl ∧ s.regs 2 = sp ∧ s.regs 3 = sl ∧
  s.regs 6 = BitVec.ofNat 64 errItab ∧ s.regs 7 = BitVec.ofNat 64 synConst ∧ 1 ≤ sl.toNat ∧ sl.toNat < 2 ^ 40 ∧
  4192 ≤ s.sp.toNat ∧ Mod R R2 T L ∧
  Env R R2 T b L (s.sp.toNat - 4192) (s.sp.toNat + 72) s ∧
  ChunkOK R R2 L b sp sl (s.sp.toNat - 4192) (s.sp.toNat + 72) s.mem

/-- the facts about the fresh error object `t` (a `*strconv.NumError`) and the fresh copy `q` of the string `(sp, sl)` that
`strconv.toError` builds for an `ErrSyntax` failure with function name `(fp, fl)`: `Func = (fp, fl)`, `Num = (q, sl)`,
`Err = strconv.ErrSyntax` (the variable's value in `s.mem`), both objects fresh and live in `s'`. -/
def TeObj (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) (q t : Nat) : Prop :=
  InRanges q (blockSize sl.toNat true) R.rt ∧ InRanges t (blockSize 48 false) R.rt ∧
  ApartAll q (blockSize sl.toNat true) L ∧ ApartAll t (blockSize 48 false) (L ++ [(q, q + blockSize sl.toNat true)]) ∧
  s'.mem.readLE t 8 = fp.toNat ∧ s'.mem.readLE (t + 8) 8 = fl.toNat ∧ s'.mem.readLE (t + 16) 8 = q ∧
  s'.mem.readLE (t + 24) 8 = sl.toNat ∧ s'.mem.readLE (t + 32) 8 = s.mem.readLE strconvErrSyntax 8 ∧
  s'.mem.readLE (t + 40) 8 = s.mem.readLE (strconvErrSyntax + 8) 8 ∧
  (∀ k, k < sl.toNat → s'.mem.readLE (q + k) 1 = s.mem.readLE (sp.toNat + k) 1) ∧
  R.inv (b - blockSize sl.toNat true - blockSize 48 false)
    (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) (s.regs 28).toNat
    (view R.rt (L ++ [(q, q + blockSize sl.toNat true), (t, t + blockSize 48 false)]) s'.mem)

def TePost (R : RtInv) (R2 : IfaceModel) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  (∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 numErrItab ∧ s'.regs 1 = t ∧ TeObj R b L fp fl sp sl s s' q t.toNat) ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(s.sp.toNat - 4192, s.sp.toNat + 72)]) ∧
  s'.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ s'.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8

end Fv256.Arm64.SfdToError
