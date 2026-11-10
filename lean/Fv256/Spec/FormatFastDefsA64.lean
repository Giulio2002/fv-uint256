import Janus
import Fv256.Spec.C
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64

namespace Fv256.FormatFastA64

/-- the frame list of the fast path: the callee windows below the saved slots `[r - stack, r - 8)` and the argument area
`[r + 8, r + 40)` and the spill slots `[r + 88, r + 116)` (the saved `x29` at `r - 8` and `x30` at `r` are outside) -/
def FL (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  rt ++ [(r - stack, r - 8), (r + 8, r + 40), (r + 88, r + 116)]

open Janus.Contracts.ICall in
/-- the `Width` call answered with the `ok` result `j1` (low bit of `x1`) -/
def WRes (RW : Res) (data : BitVec 64) (fW : Nat) (r3 j1 : BitVec 64) : Prop :=
  ∃ j0 j2, RW data (BitVec.ofNat 64 fW) data r3 j0 j1 j2

open Janus.Contracts.ICall in
/-- the `Precision` call answered with an `ok` result `j1` satisfying `p` -/
def PRes (RP : Res) (data : BitVec 64) (fP : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r2 r3 j0 j1 j2, RP data (BitVec.ofNat 64 fP) r2 r3 j0 j1 j2 ∧ p j1

open Janus.Contracts.ICall in
/-- the `Flag(c)` call answered with a result `x0 = j0` satisfying `p j0` -/
def FRes (RF : Res) (data : BitVec 64) (fF c : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r3 j0 j1 j2, RF data (BitVec.ofNat 64 c) (BitVec.ofNat 64 fF) r3 j0 j1 j2 ∧ p j0

open Janus.Contracts.ICall in
/-- every query answered "plain": no width, no precision, none of the five flags (the machine tests bit 0 of the result) -/
def PlainHist (RW RP RF : Res) (data : BitVec 64) (fW fP fF : Nat) (r3 j1 : BitVec 64) : Prop :=
  ((((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 2 = 0)

open Janus.Contracts.ICall in
/-- the answers the machine acted on when it left the query chain for the big path (first non-plain answer, or a verb outside `d v s x`) -/
def NotPlain (RW RP RF : Res) (data : BitVec 64) (fW fP fF : Nat) (r3 : BitVec 64) (ch : Nat) : Prop :=
  (∃ j1, WRes RW data fW r3 j1 ∧ j1.toNat % 2 ≠ 0) ∨
  (∃ j1, (WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, (((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, (((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, PlainHist RW RP RF data fW fP fF r3 j1 ∧ ch ≠ 100 ∧ ch ≠ 115 ∧ ch ≠ 118 ∧ ch ≠ 120)

/-- the call-site property of the fast path's `Write(p []byte)` call: the receiver data word, the slice `(ptr, len, cap)` whose
first `len` bytes are readable and equal `bs`, and `len ≤ cap` -/
def FastWP (data : BitVec 64) (bs : List Nat) (sc : State) : Prop :=
  sc.regs 0 = data ∧ Janus.Contracts.StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat bs ∧
    (sc.regs 2).toNat ≤ (sc.regs 3).toNat

end Fv256.FormatFastA64
