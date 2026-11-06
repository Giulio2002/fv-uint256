import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RlpSpec
import Fv256.RlpLemmas

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the type descriptors the two kinds of allocation use (`[33]byte`, then `[1]byte`): inside the extraction's data object -/
def tyBig : Nat := dataBase Extracted.program 0
def tyOne : Nat := dataBase Extracted.program 0 + 0xC0

/-- the call-site property of the `Write` call: the receiver data word, the slice `(ptr, len, cap)` holding the RLP bytes -/
def WP (z : BitVec 64) (w : BitVec 64) (sc : State) : Prop :=
  sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
    (sc.regs 7).toNat = (sc.regs 1).toNat

/-- what `EncodeRLP` establishes -/
def EPost (rt : List (Nat × Nat)) (stack : Nat) (R : Res) (z w : BitVec 64) (s s' : State) : Prop :=
  (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2) ∧
    (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
    MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)])

/-- the state at the join after the `BitLen` chain (`EncodeRLP+0xa0`): `bl` is the bit length, in `RDX` -/
def EJ (z tab w : BitVec 64) (s S : State) (bl : Nat) : Prop :=
  S.rip = BitVec.ofNat 64 (Extracted.entry + 0xa0) ∧ S.regs 0 = z ∧ S.regs 2 = BitVec.ofNat 64 bl ∧
    S.regs 4 = s.regs 4 - 48#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.regs 14 = s.regs 14 ∧ S.xmm = s.xmm ∧ S.df = s.df ∧
    MemFrame s.mem S.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 32)] ∧
    S.mem.regions = s.mem.regions ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = tab.toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 24) 8 = w.toNat ∧ S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat

end Fv256.Amd64.EncodeRLP
