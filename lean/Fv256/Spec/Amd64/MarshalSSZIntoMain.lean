import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf
  Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.PoolAmd64
  Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Fv256.Amd64.MarshalSSZIntoMain

abbrev ev : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBadBufferLength»

abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»

abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»

abbrev tInt : Nat := Extracted.dataAddr.«type:int»

abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

def fmtAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x88)

/-- The text of the error: the `ErrBadBufferLength` text, then `": have n, want 32 bytes"`. -/
def errMsg (txt : List Nat) (n : Nat) : List Nat :=
  txt ++ ([58, 32, 104, 97, 118, 101, 32] ++ natBytes n ++ [44, 32, 119, 97, 110, 116, 32] ++ [51, 50] ++ [32, 98, 121, 116, 101, 115])

/-- `ErrBadBufferLength` holds an `*errors.errorString` (itab word, non-nil data word `e` pointing at the string header `(tp, tl)`). -/
def ErrHolds (m : Janus.Arm64.Memory) (e tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = iErr ∧ m.readLE (ev + 8) 8 = e ∧ e ≠ 0 ∧
    m.accessible e 16 false = true ∧ m.readLE e 8 = tp ∧ m.readLE (e + 8) 8 = tl ∧ e + 16 ≤ 2 ^ 48 ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)

/-- The bytes `[a, a+n)` are outside the stack window and either outside the runtimes' ranges or inside a live object. -/
def Untouched (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (s : State) (a n : Nat) : Prop :=
  (a + n ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ a) ∧ (Outside a n (R.rt ++ Ri.priv) ∨ InRanges a n L)

def ErrPre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4200 ∧ StackWritable s 4200 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem e tp tl ∧
    Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24) :: R.rt) ∧
    LiveSep [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)] R.rt ∧ LiveSep L [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)] ∧
    R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, (s.regs 4).toNat - 56, 3, 3] ∧
    R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 2 * (tl + 24) + 48 ≤ bud ∧
    (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length (R.rt ++ Ri.priv)) ∧
    Outside ev 16 (R.rt ++ Ri.priv) ∧ Outside e 16 (R.rt ++ Ri.priv) ∧
    (ev + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ ev) ∧ (e + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ e) ∧
    (tp + tl ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ tp) ∧
    (tl = 0 ∨ Outside tp tl (R.rt ++ Ri.priv) ∨ InRanges tp tl L) ∧
    CallerOK Ri s 104 24 ∧ H [len.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 104) (Janus.Contracts.rtView Ri.priv s.mem) ∧
    Outside ((s.regs 4).toNat - 4200) 4224 Ri.priv ∧ (∀ r ∈ Ri.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ LiveSep L Ri.priv ∧ Outside 0 1 Ri.priv ∧ Ri.depth ≤ 4096 ∧
    Untouched R Ri L s z.toNat 32 ∧ Untouched R Ri L s dp.toNat cap.toNat

def ErrPost (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = 0#64 ∧ s'.regs 3 = 0#64 ∧ s'.regs 1 = 0#64 ∧ (s'.regs 7).toNat = iWrap ∧
    ∃ d, (s'.regs 6).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧ s'.mem.accessible d 32 true = true ∧
      s'.mem.readLE (d + 8) 8 = (errMsg (strBytes s.mem tp tl) len.toNat).length ∧
      strBytes s'.mem (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length = errMsg (strBytes s.mem tp tl) len.toNat ∧
      s'.mem.readLE (d + 16) 8 = s.mem.readLE ev 8 ∧ s'.mem.readLE (d + 24) 8 = s.mem.readLE (ev + 8) 8 ∧
      FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
      MemFrame s.mem s'.mem (R.rt ++ (Ri.priv ++ [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)])) ∧ LiveFrame s.mem s'.mem L [] ∧
      R.inv (bud - (2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48))
        (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length))
        (s.regs 14).toNat
        (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length)) s'.mem) ∧
      s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 ∧ s'.mem.readLE dp.toNat cap.toNat = s.mem.readLE dp.toNat cap.toNat

def SuccPre (z dp : BitVec 64) (s : State) : Prop :=
  Buffer s z 32 false ∧ Buffer s dp 32 true ∧
    (z.toNat + 32 ≤ dp.toNat ∨ dp.toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (dp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat)

def SuccPost (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 3 = len - 32#64 ∧
    s'.regs 1 = cap - 32#64 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
    s'.mem.readLE dp.toNat 32 = valueAt s z 32 ∧
    Janus.MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
      ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]

def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
    (32 ≤ len.toNat → SuccPre z dp s) ∧ (len.toNat < 32 → ErrPre R Ri H L bud e tp tl z dp len cap s)

def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (32 ≤ len.toNat → SuccPost z dp len cap s s') ∧ (len.toNat < 32 → ErrPost R Ri L bud e tp tl z dp len cap s s')

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64

abbrev cAddrE : Nat := Extracted.program.contractAddr "fmt.errorf"

abbrev cAddrC : Nat := Extracted.program.contractAddr "runtime.convT64"

end Witness

end Fv256.Amd64.MarshalSSZIntoMain
