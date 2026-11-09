import Extracted
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Errorf Janus.Contracts Janus.Contracts.Errorf
  Janus.Contracts.Iface Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZIntoMain

abbrev ev : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBadBufferLength»

abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»

abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»

abbrev tInt : Nat := Extracted.dataAddr.«type:int»

abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

def fmtAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x6c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).MarshalSSZInto" 27)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).MarshalSSZInto" 28) 0

/-- The text of the error: the `ErrBadBufferLength` text, then `": have n, want 32 bytes"`. -/
def errMsg (txt : List Nat) (n : Nat) : List Nat :=
  txt ++ ([58, 32, 104, 97, 118, 101, 32] ++ natBytes n ++ [44, 32, 119, 97, 110, 116, 32] ++ [51, 50] ++ [32, 98, 121, 116, 101, 115])

/-- `ErrBadBufferLength` holds an `*errors.errorString` (itab word, non-nil data word `e` pointing at the string header `(tp, tl)`). -/
def ErrHolds (m : Memory) (e tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = iErr ∧ m.readLE (ev + 8) 8 = e ∧ e ≠ 0 ∧
    m.accessible e 16 false = true ∧ m.readLE e 8 = tp ∧ m.readLE (e + 8) 8 = tl ∧ e + 16 ≤ 2 ^ 48 ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)

/-- The bytes `[a, a+n)` are outside the stack window and either outside the runtimes' ranges or inside a live object. -/
def Untouched (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (s : State) (a n : Nat) : Prop :=
  (a + n ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ a) ∧ (Outside a n (R.rt ++ Ri.priv) ∨ InRanges a n L)

def ErrPre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 4208 ∧ StackOK s 4208 24 ∧ Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem e tp tl ∧
    Outside ((s.regs 28).toNat + 16) 8 ((s.sp.toNat - 4208, s.sp.toNat + 24) :: R.rt) ∧
    LiveSep [(s.sp.toNat - 4208, s.sp.toNat + 24)] R.rt ∧ LiveSep L [(s.sp.toNat - 4208, s.sp.toNat + 24)] ∧
    R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, s.sp.toNat - 56, 3, 3] ∧
    R.inv bud L (s.regs 28).toNat (view R.rt L s.mem) ∧ 2 * (tl + 24) + 48 ≤ bud ∧
    (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length (R.rt ++ Ri.priv)) ∧
    Outside ev 16 (R.rt ++ Ri.priv) ∧ Outside e 16 (R.rt ++ Ri.priv) ∧
    (ev + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ ev) ∧ (e + 16 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ e) ∧
    (tp + tl ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 24 ≤ tp) ∧
    (tl = 0 ∨ Outside tp tl (R.rt ++ Ri.priv) ∨ InRanges tp tl L) ∧
    CallerOK Ri s 112 24 ∧ H [len.toNat] (s.regs 28).toNat (s.sp.toNat - 112) (rtView Ri.priv s.mem) ∧
    Outside (s.sp.toNat - 4208) 4232 Ri.priv ∧ (∀ r ∈ Ri.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ LiveSep L Ri.priv ∧ Outside 0 1 Ri.priv ∧ Ri.depth ≤ 4096 ∧
    Untouched R Ri L s z.toNat 32 ∧ Untouched R Ri L s dp.toNat cap.toNat

def ErrPost (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = 0#64 ∧ s'.regs 1 = 0#64 ∧ s'.regs 2 = 0#64 ∧ (s'.regs 3).toNat = iWrap ∧
    ∃ d, (s'.regs 4).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧ s'.mem.accessible d 32 true = true ∧
      s'.mem.readLE (d + 8) 8 = (errMsg (strBytes s.mem tp tl) len.toNat).length ∧
      strBytes s'.mem (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length = errMsg (strBytes s.mem tp tl) len.toNat ∧
      s'.mem.readLE (d + 16) 8 = s.mem.readLE ev 8 ∧ s'.mem.readLE (d + 24) 8 = s.mem.readLE (ev + 8) 8 ∧
      FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
      MemFrame s.mem s'.mem (R.rt ++ (Ri.priv ++ [(s.sp.toNat - 4208, s.sp.toNat + 24)])) ∧ LiveFrame s.mem s'.mem L [] ∧
      R.inv (bud - (2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48))
        (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length))
        (s.regs 28).toNat
        (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length)) s'.mem) ∧
      s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 ∧ s'.mem.readLE dp.toNat cap.toNat = s.mem.readLE dp.toNat cap.toNat

def SuccPre (z dp : BitVec 64) (s : State) : Prop :=
  Ptr32 s.mem z false ∧ Ptr32 s.mem dp true ∧
    Disjoint z.toNat 32 dp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
    Disjoint dp.toNat 32 (s.sp.toNat - 120) 144

def SuccPost (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 1 = len - 32#64 ∧
    s'.regs 2 = cap - 32#64 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
    s'.mem.readLE dp.toNat 32 = val256 s.mem z.toNat ∧
    MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]

def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s : State) : Prop :=
  GuardOK s 0 ∧ StackOK s 120 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧ s.regs 29 = s.sp - 8#64 ∧
    (32 ≤ len.toNat → SuccPre z dp s) ∧ (len.toNat < 32 → ErrPre R Ri H L bud e tp tl z dp len cap s)

def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z dp len cap : BitVec 64) (s s' : State) : Prop :=
  (32 ≤ len.toNat → SuccPost z dp len cap s s') ∧ (len.toNat < 32 → ErrPost R Ri L bud e tp tl z dp len cap s s')

end Fv256.Arm64.MarshalSSZIntoMain
