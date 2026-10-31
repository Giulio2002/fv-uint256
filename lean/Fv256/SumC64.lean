import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# Callee summaries (amd64), family C

`SetFromBig` and `Cmp` as callees of other functions, as in `Fv256.SumC` (arm64).
-/

namespace Fv256.C

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

/-- the call state facts every callee summary shares: the return-address slot is readable and canonical. -/
def RetOK (s : State) : Prop :=
  s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 ∧
    s.xmm 15 = 0 ∧ s.df = false

/-- what a leaf callee preserves. -/
def Kept (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
    s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase

/-- `SetFromBig(z, b)` as a callee (`z` in `RAX`, `b` in `RBX`). -/
def SfbSummary64 (p : Janus.Amd64.Program) (entry : Nat) (z b pw len : BitVec 64) : Prop :=
  Summary p entry
    (fun s => RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = b ∧ Buffer s z 32 true ∧ Buffer s b 32 false ∧
      s.mem.readLE b.toNat 1 < 2 ∧
      s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
      Buffer s pw (8 * len.toNat) false ∧
      Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * len.toNat) ∧ Disjoint z 32 (s.regs 4) 8)
    (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
      s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
      (s'.regs 0).toNat % 256 = (if fromBigOv len.toNat then 1 else 0) ∧
      s'.mem.readLE z.toNat 8 + 2 ^ 64 * s'.mem.readLE (z.toNat + 8) 8 + 2 ^ 128 * s'.mem.readLE (z.toNat + 16) 8 +
          2 ^ 192 * s'.mem.readLE (z.toNat + 24) 8 =
        fromBig (s.mem.readLE b.toNat 1 == 1) (bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
      MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)])

/-- `Cmp(z, y)` as a callee (`z` in `RAX`, `y` in `RBX`). -/
def CmpSummary64 (p : Janus.Amd64.Program) (entry : Nat) (z y : BitVec 64) : Prop :=
  Summary p entry
    (fun s => RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = y ∧ Buffer s z 32 false ∧ Buffer s y 32 false)
    (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
      s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
      s'.regs 0 = BitVec.ofInt 64 (Spec.cmp (s.mem.readLE z.toNat 32) (s.mem.readLE y.toNat 32)) ∧
      s'.mem = s.mem)

end Fv256.C
