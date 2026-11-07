import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RlpSpec
import Fv256.RlpLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the type descriptors the two kinds of allocation use (`[33]byte`, then `[1]byte`): the `ADRP`+`ADD` pairs at `+0x9c`, `+0x144` -/
def tyBig : Nat :=
  adrpLdTarget (Extracted.entry + 0x9c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 39)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 40) 0
def tyOne : Nat :=
  adrpLdTarget (Extracted.entry + 0x144) (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 81)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).EncodeRLP" 82) 0

/-- the call-site property of the `Write` call: the receiver data word, the slice `(ptr, len, cap)` holding the RLP bytes -/
def WP (z w : BitVec 64) (sc : State) : Prop :=
  sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
    (sc.regs 3).toNat = (sc.regs 2).toNat

/-- what `EncodeRLP` establishes -/
def EPost (rt : List (Nat × Nat)) (stack : Nat) (R : Res) (z w : BitVec 64) (s s' : State) : Prop :=
  (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2) ∧
    (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
    MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)])

/-- the state at the join after the `BitLen` chain (`EncodeRLP+0x88`): `bl` is the bit length, in `X3` -/
def EJ (z tab w : BitVec 64) (ret : Nat) (s S : State) (bl : Nat) : Prop :=
  S.pc = BitVec.ofNat 64 (Extracted.entry + 0x88) ∧ S.regs 0 = z ∧ S.regs 3 = BitVec.ofNat 64 bl ∧
    S.sp = s.sp - 64#64 ∧ S.regs 29 = s.sp - 72#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 18 = s.regs 18 ∧
    MemFrame s.mem S.mem [(s.sp.toNat - 72, s.sp.toNat - 56), (s.sp.toNat + 16, s.sp.toNat + 32)] ∧
    S.mem.regions = s.mem.regions ∧ S.mem.readLE (s.sp.toNat + 16) 8 = tab.toNat ∧
    S.mem.readLE (s.sp.toNat + 24) 8 = w.toNat ∧ S.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat ∧
    S.mem.readLE (s.sp.toNat - 64) 8 = ret

theorem off_ok (z k : Nat) (hk : k + 8 ≤ 32) : z + k + 8 ≤ z + 32 := by omega
theorem off_ok0 (z : Nat) : z + 8 ≤ z + 32 := by omega
theorem le_off (z k : Nat) : z ≤ z + k := Nat.le_add_right z k

/-- a sub-range of `*z` is outside the newobject frame ranges -/
theorem out_z {rt : List (Nat × Nat)} {z a n sp stack : Nat} (hzo : Outside z 32 rt)
    (hzd : z + 32 ≤ sp - 64 - stack ∨ sp - 64 - stack + (stack + 96) ≤ z) (h4104 : 4104 ≤ stack) (hwb : 64 + stack ≤ sp)
    (h1 : z ≤ a) (h2 : a + n ≤ z + 32) :
    Outside a n (rt ++ [(sp - 64 - 4096, sp - 64 - 8), (sp - 64 + 8, sp - 64 + 8 + 8)]) := by
  simp only [outside_append, outside_cons, outside_nil]
  refine ⟨hzo.of_sub h1 h2, ?_, ?_, trivial⟩ <;> omega

/-- a sub-range of `*z` is outside the join frame ranges -/
theorem out_z2 {z a n sp stack : Nat} (hzd : z + 32 ≤ sp - 64 - stack ∨ sp - 64 - stack + (stack + 96) ≤ z)
    (h4104 : 4104 ≤ stack) (hwb : 64 + stack ≤ sp) (h1 : z ≤ a) (h2 : a + n ≤ z + 32) :
    Outside a n [(sp - 72, sp - 56), (sp + 16, sp + 32)] := by
  simp only [outside_cons, outside_nil]
  refine ⟨?_, ?_, trivial⟩ <;> omega

theorem epost_ex {R : Res} {w : BitVec 64} {s' : State} {a b c d e1 e2 : BitVec 64} (hR : R w a b c d e1 e2)
    (h0 : s'.regs 0 = e1) (h3 : s'.regs 1 = e2) :
    ∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2 :=
  ⟨_, _, _, _, _, _, hR, h0, h3⟩

theorem epost_of {rt : List (Nat × Nat)} {stack : Nat} {R : Res} {z w : BitVec 64} {s s' : State}
    (hex : ∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2)
    (hF : MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)]))
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat) :
    EPost rt stack R z w s s' := by
  have hout : Outside z.toNat 32 (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)]) := by
    simp only [outside_append, outside_cons, outside_nil]
    refine ⟨hzo, ?_, trivial⟩ <;> omega
  have h := hF.readLE z.toNat 32 hout
  unfold EPost
  exact And.intro hex (And.intro (fun _ => h) hF)

end Fv256.Arm64.EncodeRLP
