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

theorem off_ok (z k : Nat) (hk : k + 8 ≤ 32) : z + k + 8 ≤ z + 32 := by omega
theorem off_ok0 (z : Nat) : z + 8 ≤ z + 32 := by omega
theorem le_off (z k : Nat) : z ≤ z + k := Nat.le_add_right z k

/-- a sub-range of `*z` is outside the newobject frame ranges (the callee's window and the spill slot of the return address) -/
theorem out_z {rt : List (Nat × Nat)} {z a n rsp stack : Nat} (hzo : Outside z 32 rt)
    (hzd : z + 32 ≤ rsp - 56 - stack ∨ rsp + 32 ≤ z) (h4104 : 4104 ≤ stack) (hwb : 56 + stack ≤ rsp)
    (h1 : z ≤ a) (h2 : a + n ≤ z + 32) :
    Outside a n (rt ++ [(rsp - 56 - 4096, rsp - 56), (rsp - 56 + 8, rsp - 56 + 8 + 8)]) := by
  simp only [outside_append, outside_cons, outside_nil]
  refine ⟨hzo.of_sub h1 h2, ?_, ?_, trivial⟩ <;> omega

/-- a sub-range of `*z` is outside the join frame ranges -/
theorem out_z2 {z a n rsp stack : Nat} (hzd : z + 32 ≤ rsp - 56 - stack ∨ rsp + 32 ≤ z) (hwb : 56 + stack ≤ rsp)
    (h1 : z ≤ a) (h2 : a + n ≤ z + 32) :
    Outside a n [(rsp - 8, rsp), (rsp + 16, rsp + 32)] := by
  simp only [outside_cons, outside_nil]
  refine ⟨?_, ?_, trivial⟩ <;> omega

theorem epost_ex {R : Res} {w : BitVec 64} {s' : State} {a b c d e1 e2 : BitVec 64} (hR : R w a b c d e1 e2)
    (h0 : s'.regs 0 = e1) (h3 : s'.regs 3 = e2) :
    ∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2 :=
  ⟨_, _, _, _, _, _, hR, h0, h3⟩

theorem epost_of {rt : List (Nat × Nat)} {stack : Nat} {R : Res} {z w : BitVec 64} {s s' : State}
    (hex : ∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2)
    (hF : MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)]))
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat) :
    EPost rt stack R z w s s' := by
  have hout : Outside z.toNat 32 (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)]) := by
    simp only [outside_append, outside_cons, outside_nil]
    refine ⟨hzo, ?_, trivial⟩ <;> omega
  have h := hF.readLE z.toNat 32 hout
  unfold EPost
  exact And.intro hex (And.intro (fun _ => h) hF)

end Fv256.Amd64.EncodeRLP
