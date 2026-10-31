import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# Callee summaries (arm64), family C

`SetFromBig` and `Cmp` as callees of other functions (`CmpBig`, `FromBig`, `MustFromBig`): `Summary` statements in terms of
the independent specification, parametrised by the program they are proved in.
-/

namespace Fv256.C

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

/-- the preconditions on a `big.Int` at `x` with word array `(pw, len)`. -/
def BigAt (s : State) (x pw len : BitVec 64) : Prop :=
  Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
  s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
  Ptr s.mem pw (8 * len.toNat) false

/-- `SetFromBig(z, x)` as a callee. -/
def SfbSummary (p : Program) (entry : Nat) (pw len : BitVec 64) : Prop :=
  Summary p entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧
      Ptr32 s.mem (s.regs 0) true ∧ BigAt s (s.regs 1) pw len ∧
      Disjoint (s.regs 0).toNat 32 (s.regs 1).toNat 32 ∧ Disjoint (s.regs 0).toNat 32 pw.toNat (8 * len.toNat))
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
      (s'.regs 0).toNat = (if fromBigOv len.toNat then 1 else 0) ∧
      val256 s'.mem (s.regs 0).toNat =
        fromBig (s.mem.readLE (s.regs 1).toNat 1 == 1) (bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
      MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32)])

/-- `Cmp(z, y)` as a callee (`z` in `X0`, `y` in `X1`). -/
def CmpSummary (p : Program) (entry : Nat) (z y : BitVec 64) : Prop :=
  Summary p entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.regs 0 = z ∧ s.regs 1 = y ∧
      Ptr32 s.mem z false ∧ Ptr32 s.mem y false)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
      s'.regs 0 = BitVec.ofInt 64 (Spec.cmp (val256 s.mem z.toNat) (val256 s.mem y.toNat)) ∧
      s'.mem = s.mem)

end Fv256.C
