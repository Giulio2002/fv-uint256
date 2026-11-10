import Extracted
import Fv256.Spec.C
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Iface
  Janus.Spec Janus.Spec.Type

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySimpa false

set_option linter.janusRenameI false

set_option linter.unusedVariables false

namespace Fv256.Arm64.FormatNil

/-- the type-assertion descriptor `uint256..typeAssert.0` -/
def descA : Nat := Extracted.dataAddr.«github.com/holiman/uint256..typeAssert.0»

/-- the type descriptor of `string` (the `any` word of the argument) -/
def strTyA : Nat := Extracted.dataAddr.«type:string#f88732b8»

/-- the static string header of `"<nil>"` (the data word of the argument) -/
def hdrA : Nat := Extracted.dataAddr.«.rodata#9732ef5a»

/-- the address of the bytes `"<nil>"` (the first word of that header; the bytes themselves are not part of the extraction) -/
def litA : Nat := dataWord Extracted.program.data ".rodata+0x360c8" 0 8

/-- the itab `Type` word of the incoming `fmt.State` -/
def tyOf (S0 : State) (tab : BitVec 64) : Nat := S0.mem.readLE (tab.toNat + 8) 8

/-- the itab `getitab` answers for `s.(io.Writer)`: nil for a nil `s` -/
def wOf (R : IfaceModel) (S0 : State) (tab : BitVec 64) : Nat :=
  if tab.toNat = 0 then 0 else (R.itab (taInter S0.mem descA) (tyOf S0 tab)).getD 0

/-- the memory `runtime.typeAssert` may touch -/
def TAFL (R : IfaceModel) (sp : Nat) : List (Nat × Nat) :=
  R.priv ++ [(sp - R.depth, sp - 8), (sp + 8, sp + 8 + 8 * 2)] ++ [(descA, descA + 8)]

/-- the memory the whole path may touch -/
def NilFL (R : IfaceModel) (rt : List (Nat × Nat)) (sp stack : Nat) : List (Nat × Nat) :=
  rt ++ TAFL R sp ++ [(sp - stack, sp - 8), (sp + 8, sp + 8 + 8 * 5), (sp + 56, sp + 72)]

/-- the call-site property of `fmt.Fprint(w, "<nil>")` -/
def FpArg (data : BitVec 64) (sc : State) : Prop :=
  sc.regs 1 = data ∧ sc.regs 3 = 1#64 ∧ sc.regs 4 = 1#64 ∧ (sc.regs 2).toNat = sc.sp.toNat + 56 ∧
  sc.mem.readLE (sc.regs 2).toNat 8 = strTyA ∧ sc.mem.readLE ((sc.regs 2).toNat + 8) 8 = hdrA ∧
  sc.mem.readLE hdrA 8 = litA ∧ sc.mem.readLE (hdrA + 8) 8 = 5 ∧ StrOut sc.mem litA 5 Fv256.FormatSpec.nilText

end Fv256.Arm64.FormatNil
