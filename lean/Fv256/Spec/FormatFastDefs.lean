import Janus
import Fv256.Spec.C
import Fv256.Spec.E
import Fv256.Spec.FormatBytes

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus

namespace Fv256.FormatFast

/-- the frame list of the fast path: the callee windows `[r - 8 - stack, r + 32)` and the spill slots `[r + 0x50, r + 0x6c)` -/
def FL (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  rt ++ [(r - 8 - stack, r + 32), (r + 0x50, r + 0x6c)]

end Fv256.FormatFast

namespace Fv256.FormatFast

open Janus.Amd64

/-- the call-site property of the fast path's `Write(p []byte)` call: the receiver data word, the slice `(ptr, len, cap)` whose
first `len` bytes are readable and equal `bs`, and `len ≤ cap` -/
def FastWP (data : BitVec 64) (bs : List Nat) (sc : State) : Prop :=
  sc.regs 0 = data ∧ Janus.Contracts.StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat bs ∧
    (sc.regs 1).toNat ≤ (sc.regs 7).toNat

end Fv256.FormatFast

namespace Fv256.FormatFast

open Janus.Amd64

open Janus.Contracts.ICall in
/-- the `Width` call answered with result byte `j3` (low byte of `RBX`) -/
def WRes (RW : Res) (data tab rW j3 : BitVec 64) : Prop := ∃ j0 j1, RW data tab data rW j0 j3 j1

open Janus.Contracts.ICall in
/-- the `Precision` call (receiver `data`, `RBX` = `b3` left over from `Width`) answered with `p j3` -/
def PRes (RP : Res) (data b3 : BitVec 64) (fP : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ p j3

open Janus.Contracts.ICall in
/-- the `Flag(c)` call answered with a result `RAX = j0` satisfying `p j0` -/
def FRes (RF : Res) (data : BitVec 64) (fF c : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 c) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ p j0

/-- the machine reads `Flag('+')`, `Flag(' ')`, `Flag('0')` as true iff the result byte is nonzero -/
def fz (j0 : BitVec 64) : Prop := j0.toNat % 256 = 0

/-- the machine reads `Flag('-')`, `Flag('#')` as true iff the result byte is exactly 1 -/
def fx (j0 : BitVec 64) : Prop := j0.toNat % 256 ≠ 1

open Janus.Contracts.ICall in
/-- every query answered "plain": no width, no precision, none of the five flags (as the machine decides) -/
def PlainHist (RW RP RF : Res) (data tab rW j3 : BitVec 64) (fP fF : Nat) : Prop :=
  ((((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧ FRes RF data fF 0x30 fz) ∧
    FRes RF data fF 0x23 fx

end Fv256.FormatFast
