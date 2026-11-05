import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdEnv

/-!
# `strconv.toError(fn, s, base, bitSize, err)` for `err == ErrSyntax` (amd64), as a callee of `strconv.ParseUint`

`ParseUint` calls `toError("ParseUint", s, 10, 64, err)` when the internal parser fails; for a syntax failure the
result is `&NumError{Func: fn, Num: cloneString(s), Err: strconv.ErrSyntax}` (a freshly allocated object, the
string copied by `mallocgc` + `memmove`).  The runtime calls are `runtime.ifaceeq` (the comparison
`err == ErrSyntax`, interface-model contract), `runtime.mallocgc`, `runtime.memmove`, `runtime.newobject` and the
write barriers (live contracts, all threaded through one `RtInv`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.Amd64.SfdEnv

namespace Fv256.Amd64.SfdToError

abbrev te : Nat := segAddr Extracted.program "strconv.toError"



open Fv256.C in
def TePre (R : RtInv) (R2 : IfaceModel) (T : Nat) (b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = fp ∧ s.regs 3 = fl ∧ s.regs 1 = sp ∧ s.regs 7 = sl ∧
  s.regs 9 = BitVec.ofNat 64 errItab ∧ s.regs 10 = BitVec.ofNat 64 synConst ∧
  1 ≤ sl.toNat ∧ sl.toNat < 2 ^ 40 ∧
  StackGuardOK s 4192 ∧ StackWritable s 4192 72 ∧ (s.regs 4).toNat % 8 = 0 ∧
  Extracted.program.DataLoaded s.mem ∧
  R2.depth ≤ 4096 ∧ CallerOK R2 s 96 72 ∧
  Outside ((s.regs 4).toNat - 4192) 4264 R.rt ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)]) ∧
  blockSize sl.toNat true + blockSize 48 false ≤ b ∧
  s.mem.readLE (errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory s.mem T = true ∧ isDirectIface s.mem T = false ∧
  tySize s.mem T = 8 ∧
  Outside errItab 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside synConst 8 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside strconvErrSyntax 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside wbFlag 4 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  Outside numErrType 16 [((s.regs 4).toNat - 4192, (s.regs 4).toNat + 72)] ∧
  (∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ (∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv) ∧
  Outside numErrType 16 R.rt ∧ Outside wbFlag 4 R.rt ∧
  R.ok (Extracted.program.contractAddr "runtime.mallocgc") [sl.toNat, 0, 0] ∧
  R.ok (Extracted.program.contractAddr "runtime.newobject") [numErrType] ∧
  (∀ q, R.ok (Extracted.program.contractAddr "runtime.memmove") [q, sp.toNat, sl.toNat]) ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  s.mem.accessible sp.toNat sl.toNat false = true ∧ sp.toNat + sl.toNat ≤ 2 ^ 48 ∧
  (sp.toNat + sl.toNat ≤ (s.regs 4).toNat - 4192 ∨ (s.regs 4).toNat + 72 ≤ sp.toNat) ∧
  Spec.Disjoint ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4192) 4264 ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
  (∀ r ∈ R.rt, 0 < r.1) ∧
  Outside numErrType 16 R2.priv ∧ Outside wbFlag 4 R2.priv ∧ Outside strconvErrSyntax 16 R2.priv ∧
  s.mem.accessible wbFlag 4 false = true ∧ s.mem.accessible strconvErrSyntax 16 false = true

end Fv256.Amd64.SfdToError
