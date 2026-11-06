import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdProg
import Fv256.Arm64.SfdEnv
import Fv256.Arm64.SfdTePre
import Fv256.Arm64.SfdParse

/-!
# `strconv.ParseUint(s, 10, 64)` (the exported wrapper) on a chunk of 1 to 19 bytes (arm64): STATEMENT

STATEMENT ONLY (proof `sorry` until `te_sum` is done): consumers take `pw_sum` as a hypothesis of type `PwSum`.
Registers: in `X0 = p, X1 = len, X2 = 10, X3 = 64`; out `X0 = n`, `X1, X2 = err` (ok: `X1 = X2 = 0`).
Window `[lo, hi)`: the function's whole stack window (`Env R R2 T b L lo hi`), `lo + 4280 <= SP`, `SP + 48 <= hi`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError

namespace Fv256.Arm64.SfdPw

abbrev pw : Nat := segAddr Fv256.Arm64.SfdProg.program "strconv.ParseUint"
abbrev fnStr : Nat := 0xeb483

def PwPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
  s.regs 0 = p ∧ s.regs 1 = len ∧ s.regs 2 = 10#64 ∧ s.regs 3 = 64#64 ∧ 1 ≤ len.toNat ∧ len.toNat ≤ 19 ∧
  Mod R R2 T L ∧ Env R R2 T b L lo hi s ∧ lo + 4280 ≤ s.sp.toNat ∧ s.sp.toNat + 48 ≤ hi ∧
  ChunkOK R R2 L b p len lo hi s.mem

def PwPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (p len : BitVec 64)
    (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  ((allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧
      s'.regs 1 = 0 ∧ s'.regs 2 = 0 ∧ Env R R2 T b L lo hi s' ∧ MemFrame s.mem s'.mem [(lo, hi)]) ∨
   (¬ allDec (Fv256.C.bytesAt s.mem p.toNat) 0 len.toNat ∧ s'.regs 0 = 0 ∧
      (∃ (q : Nat) (t : BitVec 64), s'.regs 1 = BitVec.ofNat 64 numErrItab ∧ s'.regs 2 = t ∧
        TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 p len s s' q t.toNat) ∧
      MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])))

/-- the statement consumers assume (the hypotheses are the runtime contracts of the library program) -/
def PwSum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (p len : BitVec 64) : Prop :=
  Summary (P.link impl) pw (PwPre R R2 T b L lo hi p len) (PwPost R R2 T b L lo hi p len)

theorem pw_sum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (p len : BitVec 64)
    (hif : Contracts.Iface.Ifaceeq (P.link impl) (P.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (P.link impl) (P.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (P.link impl) (P.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (P.link impl) (P.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P.link impl) (P.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    PwSum impl R R2 T b L lo hi p len := by
  sorry

end Fv256.Arm64.SfdPw
