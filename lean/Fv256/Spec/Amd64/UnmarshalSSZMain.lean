import Extracted
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Tactic Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Errorf
  Janus.Contracts Janus.Contracts.Errorf Janus.Contracts.ErrorfAmd64 Janus.Contracts.PoolAmd64
  Janus.Contracts.ErrorfRealFmt Janus.Spec.Map Janus.Spec.Type Janus.Contracts.Iface Janus.Contracts.IfaceAmd64

namespace Fv256.Amd64.UnmarshalSSZMain

abbrev ev : Nat := Extracted.dataAddr.«github.com/holiman/uint256.ErrBadEncodedLength»

abbrev tErr : Nat := Extracted.dataAddr.«type:*errors.errorString»

abbrev iErr : Nat := Extracted.dataAddr.«go:itab.*errors.errorString,error»

abbrev tInt : Nat := Extracted.dataAddr.«type:int»

abbrev iWrap : Nat := Extracted.dataAddr.«go:itab.*fmt.wrapError,error»

def fmtAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x88)

/-- The text of the error: the `ErrBadEncodedLength` text, then `": have n, want 32 bytes"`. -/
def errMsg (txt : List Nat) (n : Nat) : List Nat :=
  txt ++ ([58, 32, 104, 97, 118, 101, 32] ++ natBytes n ++ [44, 32, 119, 97, 110, 116, 32] ++ [51, 50] ++ [32, 98, 121, 116, 101, 115])

/-- `ErrBadEncodedLength` holds an `*errors.errorString` (itab word, non-nil data word `e` pointing at the string header `(tp, tl)`). -/
def ErrHolds (m : Janus.Arm64.Memory) (e tp tl : Nat) : Prop :=
  m.accessible ev 16 false = true ∧ m.readLE ev 8 = iErr ∧ m.readLE (ev + 8) 8 = e ∧ e ≠ 0 ∧
    m.accessible e 16 false = true ∧ m.readLE e 8 = tp ∧ m.readLE (e + 8) 8 = tl ∧ e + 16 ≤ 2 ^ 48 ∧
    tl + 60 ≤ 2 ^ 32 ∧ tp + tl ≤ 2 ^ 48 ∧ (tl = 0 ∨ m.accessible tp tl false = true)

/-- The bytes `[a, a+n)` are outside the stack window and either outside the runtimes' ranges or inside a live object. -/
def Untouched (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (s : State) (a n : Nat) : Prop :=
  (a + n ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ a) ∧ (Outside a n (R.rt ++ Ri.priv) ∨ InRanges a n L)

def ErrPre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4200 ∧ StackWritable s 4200 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧ ErrHolds s.mem e tp tl ∧
    Outside ((s.regs 14).toNat + 16) 8 (((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24) :: R.rt) ∧
    LiveSep [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)] R.rt ∧ LiveSep L [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)] ∧
    R.ok (Extracted.program.contractAddr "fmt.errorf") [fmtAddr, 26, (s.regs 4).toNat - 56, 3, 3] ∧
    R.inv bud L (s.regs 14).toNat (view R.rt L s.mem) ∧ 2 * (tl + 42) + 48 ≤ bud ∧
    (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length (R.rt ++ Ri.priv)) ∧
    Outside ev 16 (R.rt ++ Ri.priv) ∧ Outside e 16 (R.rt ++ Ri.priv) ∧
    (ev + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ ev) ∧ (e + 16 ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ e) ∧
    (tp + tl ≤ (s.regs 4).toNat - 4200 ∨ (s.regs 4).toNat + 24 ≤ tp) ∧
    (tl = 0 ∨ Outside tp tl (R.rt ++ Ri.priv) ∨ InRanges tp tl L) ∧
    CallerOK Ri s 104 24 ∧ H [len.toNat] (s.regs 14).toNat ((s.regs 4).toNat - 104) (Janus.Contracts.rtView Ri.priv s.mem) ∧
    Outside ((s.regs 4).toNat - 4200) 4224 Ri.priv ∧ (∀ r ∈ Ri.priv, Outside r.1 (r.2 - r.1) R.rt) ∧ LiveSep L Ri.priv ∧ Outside 0 1 Ri.priv ∧ Ri.depth ≤ 4096 ∧
    Untouched R Ri L s z.toNat 32 ∧ Untouched R Ri L s bp.toNat cap.toNat

def ErrPost (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  (s'.regs 0).toNat = iWrap ∧
    ∃ d, (s'.regs 3).toNat = d ∧ d + 32 ≤ 2 ^ 48 ∧ s'.mem.accessible d 32 true = true ∧
      s'.mem.readLE (d + 8) 8 = (errMsg (strBytes s.mem tp tl) len.toNat).length ∧
      strBytes s'.mem (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length = errMsg (strBytes s.mem tp tl) len.toNat ∧
      s'.mem.readLE (d + 16) 8 = s.mem.readLE ev 8 ∧ s'.mem.readLE (d + 24) 8 = s.mem.readLE (ev + 8) 8 ∧
      FreshFrom [(d, d + 32)] L ∧ InRanges d 32 R.rt ∧
      MemFrame s.mem s'.mem (R.rt ++ (Ri.priv ++ [((s.regs 4).toNat - 4200, (s.regs 4).toNat + 24)])) ∧ LiveFrame s.mem s'.mem L [] ∧
      R.inv (bud - (2 * (errMsg (strBytes s.mem tp tl) len.toNat).length + 48))
        (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length))
        (s.regs 14).toNat
        (view R.rt (L ++ ((d, d + 32) :: range0 (s'.mem.readLE d 8) (errMsg (strBytes s.mem tp tl) len.toNat).length)) s'.mem) ∧
      s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 ∧ s'.mem.readLE bp.toNat cap.toNat = s.mem.readLE bp.toNat cap.toNat

def SuccPre (z bp : BitVec 64) (s : State) : Prop :=
  Buffer s z 32 true ∧ Buffer s bp 32 false ∧
    (z.toNat + 32 ≤ bp.toNat ∨ bp.toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (bp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ bp.toNat)

def SuccPost (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.mem.readLE z.toNat 32 = s.mem.readLE bp.toNat 32 ∧
    Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
      ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]

def Pre (R : RtInv) (Ri : IfaceModel) (H : RtReady) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
    (len.toNat = 32 → SuccPre z bp s) ∧ (len.toNat ≠ 32 → ErrPre R Ri H L bud e tp tl z bp len cap s)

def Post (R : RtInv) (Ri : IfaceModel) (L : List (Nat × Nat)) (bud e tp tl : Nat) (z bp len cap : BitVec 64) (s s' : State) : Prop :=
  (len.toNat = 32 → SuccPost z bp len cap s s') ∧ (len.toNat ≠ 32 → ErrPost R Ri L bud e tp tl z bp len cap s s')

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.ErrorfRealRt Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64

abbrev cAddrE : Nat := Extracted.program.contractAddr "fmt.errorf"

abbrev cAddrC : Nat := Extracted.program.contractAddr "runtime.convT64"

end Witness

end Fv256.Amd64.UnmarshalSSZMain
