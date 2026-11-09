import Extracted
import Fv256.Spec.Amd64.FormatBigDefs
import Fv256.Spec.Amd64.FormatFastPre
import Fv256.Spec.Amd64.FormatNil
import Fv256.Spec.DecAt
import Fv256.Spec.FormatFastDefs
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.C
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
  Janus.Spec Janus.Spec.Type Janus.Spec.Map

open Fv256.FormatFast Fv256.Amd64.FormatNil Fv256.E

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySimpa false

set_option linter.unusedVariables false

namespace Fv256.Amd64.FormatTransfer

/-- the memory the prefix writes (`r` = the entry `RSP`): the frame `[r-80, r)` and the argument spill slots `[r+16, r+32)` -/
def PFL (r : Nat) : List (Nat × Nat) := [(r - 80, r), (r + 16, r + 32)]

/-- the common call facts (the hypotheses of `prefix_nz` / `prefix_z`) -/
def PreCommon (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  StackGuardOK s 0 ∧ (s.regs 4).toNat % 8 = 0 ∧ 80 + stack ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat - 80 - stack) (stack + 0x80) true = true ∧
  Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) rt

/-- the entry facts of the fast / big side (`z ≠ 0`), the entry-state form of `FPre` and the extra hypotheses of `fast_amd64` -/
def PreFastE (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (s : State) : Prop :=
  CodePtrOK64 fW ∧ CodePtrOK64 fP ∧ CodePtrOK64 fF ∧ CodePtrOK64 fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  s.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ s.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  s.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ s.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x18 + 32 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ tab.toNat + 0x18) ∧
  z.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible z.toNat 32 false = true ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ z.toNat)

/-- the window-wide frame of the fast side, in entry terms: `rt` and the whole window `[r-80-stack, r+48)` -/
def FLE (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) := rt ++ [(r - 80 - stack, r + 48)]

/-- the readiness of the runtime over every memory that frames the state (the five `H` hypotheses of `fast_amd64`), for the state with
memory `m`, local frame `r` (= `RSP`), goroutine `g` and frame list `FRM` -/
def HypsH (H : RtReady) (rt : List (Nat × Nat)) (z : BitVec 64) (r g : Nat) (m : Memory) (FRM : List (Nat × Nat)) : Prop :=
  (∀ M, MemFrame m M FRM → 2 ^ 64 ≤ m.readLE z.toNat 32 →
      H [0, r - 8 - 0x178 + 86 + (98 - decLen (m.readLE z.toNat 32)), decLen (m.readLE z.toNat 32)] g (r - 8 - 0x178 - 8) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → 100 ≤ m.readLE z.toNat 32 → m.readLE z.toNat 32 < 2 ^ 64 →
      H [0, r - 8 - 384 - 0x20 + (24 - decLen (m.readLE z.toNat 32)), decLen (m.readLE z.toNat 32)] g (r - 8 - 384 - 0x58) (rtView rt M)) ∧
  (∀ M p l, MemFrame m M FRM → StrOut M p l (decBytes (m.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l → H [0, p, l] g (r - 8) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → ∀ n, Fv256.C.hexDigits (m.readLE z.toNat 32) n →
      H [0, r - 8 - 112 + 38 + (64 - n), n + 2] g (r - 8 - 112) (rtView rt M)) ∧
  (∀ M p l n, MemFrame m M FRM → Fv256.C.hexDigits (m.readLE z.toNat 32) n →
      StrOut M p l (Fv256.C.hexStrBytes (m.readLE z.toNat 32) n) → InRanges p l rt →
      H [0, p + 2, l - 2] g (r - 8) (rtView rt M))

/-- the extra entry facts of the fast side (`z ≠ 0`) -/
def PreFastX (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 14).toNat + 16) 8 + 0x378 < (s.regs 4).toNat - 80 ∧ Outside ((s.regs 14).toNat + 16) 8 rt ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ (s.regs 14).toNat + 16) ∧
  HypsH H rt z ((s.regs 4).toNat - 72) (s.regs 14).toNat s.mem (FLE rt (s.regs 4).toNat stack)

/-- the entry-state memory frame of the nil path: `NilFL` at `S0` and the prefix frame -/
def NilFLE (R : IfaceModel) (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  NilFL R rt (r - 72) stack ++ PFL r

/-- the entry facts of the nil side (`z = 0`), the entry form of `NilPre` -/
def PreNilE (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab : BitVec 64) (s : State) : Prop :=
  CallerOK R s 80 48 ∧
  TADescOK R s.mem descA ∧ Outside descA 24 [((s.regs 4).toNat - 80 - R.depth, (s.regs 4).toNat + 48)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ s.mem.accessible tab.toNat 0x14 false = true ∧ tyOf s tab ≠ 0 ∧ R.IsType (tyOf s tab) ∧
    (taCanFail s.mem descA = true ∨ (R.itab (taInter s.mem descA) (tyOf s tab)).isSome) ∧
    Outside (tab.toNat + 8) 8 (PFL (s.regs 4).toNat)) ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside hdrA 16 (NilFLE R rt (s.regs 4).toNat stack) ∧ Outside litA 5 (NilFLE R rt (s.regs 4).toNat stack)

/-- nil receiver: one `fmt.Fprint(w, "<nil>")` -/
def NilPost (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (NilFLE R rt (s.regs 4).toNat stack) ∧
  ∃ j0 j3 j1, RFp (BitVec.ofNat 64 (wOf R s tab)) data (BitVec.ofNat 64 ((s.regs 4).toNat - 72 + 0x30)) 1#64 j0 j3 j1

/-- fast path: all queries answered plain, `ch ∈ {d, v, s, x}`, one `Write` -/
def FastPost (rt : List (Nat × Nat)) (stack fP fF : Nat) (RW RP RF RWr : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (FL rt ((s.regs 4).toNat - 72) stack ++ PFL (s.regs 4).toNat) ∧
  (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1) ∧
  (∃ j3, PlainHist RW RP RF data tab ch j3 fP fF) ∧
  (ch.toNat % 2 ^ 32 = 100 ∨ ch.toNat % 2 ^ 32 = 115 ∨ ch.toNat % 2 ^ 32 = 118 ∨ ch.toNat % 2 ^ 32 = 120)

/-- big path: some query answered "not plain" or `ch` not a fast verb, then one `(*big.Int).Format` call -/
def BigPost (R2 : RtInv) (rt : List (Nat × Nat)) (stack fP fF : Nat) (RW RP RF RBf : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (R2.rt ++ FL rt ((s.regs 4).toNat - 72) stack ++ [((s.regs 4).toNat - 72 + 0x28, (s.regs 4).toNat - 72 + 0x30)] ++ PFL (s.regs 4).toNat) ∧
  Fv256.Amd64.FormatFast.NotPlain RW RP RF data tab ch fP fF (ch.toNat % 2 ^ 32) ∧
  ∃ P j0 j3 j1, RBf (BitVec.ofNat 64 P) tab data (BitVec.ofNat 64 (ch.toNat % 2 ^ 32)) j0 j3 j1

/-- layout facts about the callee-owned ranges `rt` (state-level, so the statement has no pure premise on `rt`) -/
def PreRt (rt : List (Nat × Nat)) : Prop :=
  (∀ r ∈ rt, 32 ≤ r.1) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) ∧
  Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ Outside 5142664 256 rt

/-- the assembly precondition, at the entry state `s` -/
def PreF (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat)) (stack b0 : Nat) (fW fP fF fWr zv : Nat)
    (z tab data : BitVec 64) (s : State) : Prop :=
  PreRt rt ∧ PreCommon rt stack s ∧
  (z.toNat = 0 → PreNilE R rt stack tab s ∧
    (tab.toNat ≠ 0 → H [descA, tyOf s tab] (s.regs 14).toNat ((s.regs 4).toNat - 80) (rtView R.priv s.mem))) ∧
  (z.toNat ≠ 0 → PreFastE rt stack z tab data fW fP fF fWr s ∧ PreFastX H rt stack z s ∧
    s.mem.readLE z.toNat 32 = zv ∧ R2.inv b0 [] (s.regs 14).toNat (view R2.rt [] s.mem) ∧
    Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) R2.rt ∧ Fv256.Amd64.FormatBig.PreBigE R2 b0 z s)

end Fv256.Amd64.FormatTransfer
