import Extracted
import Fv256.Spec.Arm64.FM.IntoBigDefs
import Fv256.Spec.Arm64.FormatNil
import Fv256.Spec.DecAt
import Fv256.Spec.FormatFastDefsA64
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.C
import Fv256.Spec.E

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Iface
  Janus.Spec.Type Janus.Spec.Map

open Fv256.FormatFastA64 Fv256.Arm64.FormatNil Fv256.E

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySimpa false

set_option linter.unusedVariables false

namespace Fv256.Arm64.FormatTransfer

/-- the memory the prefix writes (`r` = the entry `SP`) -/
def PFL (r : Nat) : List (Nat × Nat) := [(r - 88, r - 72), (r + 16, r + 32)]

/-- the common call facts (the hypotheses of `prefix_nz` / `prefix_z`) -/
def PreCommon (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  GuardOK s 0 ∧ s.sp.toNat % 16 = 0 ∧ 88 + stack ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 88 - stack) (stack + 128) true = true ∧
  Outside (s.sp.toNat - 88 - stack) (stack + 128) rt

/-- the entry facts of the fast / big side (`z ≠ 0`), the entry-state form of `FPre` -/
def PreFastE (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (s : State) : Prop :=
  CodePtrOK fW ∧ CodePtrOK fP ∧ CodePtrOK fF ∧ CodePtrOK fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  s.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ s.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  s.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ s.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x38 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ tab.toNat + 0x18) ∧
  Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ z.toNat)

/-- the window-wide frame of the fast side, in entry terms: `rt` and the whole window `[r-88-stack, r+40)` -/
def FLE (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) := rt ++ [(r - 88 - stack, r + 40)]

/-- the readiness of the runtime over every memory that frames the state (the five `H` hypotheses of `fast_arm64`), for the state with
memory `m`, local frame `r` (= `SP`), goroutine `g` and frame list `FRM` -/
def HypsH (H : RtReady) (rt : List (Nat × Nat)) (z : BitVec 64) (r g : Nat) (m : Memory) (FRM : List (Nat × Nat)) : Prop :=
  (∀ M, MemFrame m M FRM → 2 ^ 64 ≤ val256 m z.toNat →
      H [0, r - 384 + 94 + (98 - decLen (val256 m z.toNat)), decLen (val256 m z.toNat)] g (r - 384) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → 100 ≤ val256 m z.toNat → val256 m z.toNat < 2 ^ 64 →
      H [0, r - 384 - 32 + (24 - decLen (val256 m z.toNat)), decLen (val256 m z.toNat)] g (r - 384 - 96) (rtView rt M)) ∧
  (∀ M p l, MemFrame m M FRM → StrOut M p l (decBytes (val256 m z.toNat)) →
      DecAt rt 989280 1002589 960826 p l → H [0, p, l] g r (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → ∀ n, Fv256.C.hexDigits (val256 m z.toNat) n →
      H [0, r - 112 + 38 + (64 - n), n + 2] g (r - 112) (rtView rt M)) ∧
  (∀ M p l n, MemFrame m M FRM → Fv256.C.hexDigits (val256 m z.toNat) n →
      StrOut M p l (Fv256.C.hexStrBytes (val256 m z.toNat) n) → InRanges p l rt →
      H [0, p + 2, l - 2] g r (rtView rt M))

/-- the extra entry facts of the fast side (`z ≠ 0`) -/
def PreFastX (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧
  (s.regs 28).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4224 < s.sp.toNat ∧ Outside ((s.regs 28).toNat + 16) 8 rt ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
  HypsH H rt z (s.sp.toNat - 80) (s.regs 28).toNat s.mem (FLE rt s.sp.toNat stack)

/-- the entry-state memory frame of the nil path: `NilFL` at `S0` and the prefix frame -/
def NilFLE (R : IfaceModel) (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  NilFL R rt (r - 80) stack ++ PFL r

/-- the entry facts of the nil side (`z = 0`), the entry form of `NilPre` -/
def PreNilE (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab : BitVec 64) (s : State) : Prop :=
  CallerOK R s 80 40 ∧
  TADescOK R s.mem descA ∧ Outside descA 24 [(s.sp.toNat - 80 - R.depth, s.sp.toNat + 40)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ s.mem.accessible tab.toNat 0x14 false = true ∧ tyOf s tab ≠ 0 ∧ R.IsType (tyOf s tab) ∧
    (taCanFail s.mem descA = true ∨ (R.itab (taInter s.mem descA) (tyOf s tab)).isSome) ∧
    Outside (tab.toNat + 8) 8 (PFL s.sp.toNat)) ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside hdrA 16 (NilFLE R rt s.sp.toNat stack) ∧ Outside litA 5 (NilFLE R rt s.sp.toNat stack)

/-- nil receiver: one `fmt.Fprint(w, "<nil>")` -/
def NilPost (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (NilFLE R rt s.sp.toNat stack) ∧
  ∃ j0 j1 j2, RFp (BitVec.ofNat 64 (wOf R s tab)) data (BitVec.ofNat 64 (s.sp.toNat - 80 + 56)) 1#64 j0 j1 j2

/-- fast path: all queries answered plain, `ch ∈ {d, v, s, x}`, one `Write` -/
def FastPost (rt : List (Nat × Nat)) (stack fW fP fF : Nat) (RW RP RF RWr : Res) (data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (FL rt (s.sp.toNat - 80) stack ++ PFL s.sp.toNat) ∧
  (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2) ∧
  (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
  (ch.toNat % 2 ^ 32 = 100 ∨ ch.toNat % 2 ^ 32 = 115 ∨ ch.toNat % 2 ^ 32 = 118 ∨ ch.toNat % 2 ^ 32 = 120)

/-- the frame of the big path, in entry terms: the allocator's ranges, the fast side's, the local slot `[S0.sp+8, S0.sp+56)` (arguments and the
`big.Int` slot) and the prefix's -/
def BigFL (R2 : RtInv) (rt : List (Nat × Nat)) (stack r : Nat) : List (Nat × Nat) :=
  R2.rt ++ FL rt (r - 80) stack ++ [(r - 72, r - 24)] ++ PFL r

/-- big path: some query answered "not plain" or `ch` not a fast verb, then one `(*big.Int).Format` call -/
def BigPost (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF : Nat) (RW RP RF RBf : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (BigFL R2 rt stack s.sp.toNat) ∧
  NotPlain RW RP RF data fW fP fF ch (ch.toNat % 2 ^ 32) ∧
  ∃ P j0 j1 j2, RBf (BitVec.ofNat 64 P) tab data
    (BitVec.ofNat 64 (if ch.toNat % 2 ^ 32 < 2 ^ 31 then ch.toNat % 2 ^ 32 else ch.toNat % 2 ^ 32 + 18446744069414584320)) j0 j1 j2

/-- layout facts about the callee-owned ranges `rt` (state-level, so the statement has no pure premise on `rt`) -/
def PreRt (rt : List (Nat × Nat)) : Prop :=
  (∀ r ∈ rt, 32 ≤ r.1) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) ∧
  Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 968614 256 rt

/-- the allocator facts of the big path (state-level: they mention the runtime model `R2`) -/
def PreBig (R2 : RtInv) (b0 : Nat) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Outside ((s.regs 28).toNat + 16) 8 R2.rt ∧ s.mem.accessible Fv256.Arm64.IntoBig.flagAddr 4 false = true ∧
  Outside Fv256.Arm64.IntoBig.bigType 16 R2.rt ∧ Outside Fv256.Arm64.IntoBig.arrType 16 R2.rt ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [Fv256.Arm64.IntoBig.bigType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [Fv256.Arm64.IntoBig.arrType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  blockSize 32 false + blockSize 32 true ≤ b0 ∧
  Outside (s.sp.toNat - 88 - stack) (stack + 128) R2.rt ∧ Outside z.toNat 32 R2.rt

/-- the assembly precondition, at the entry state `s` -/
def PreF (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat)) (stack b0 fW fP fF fWr zv : Nat)
    (z tab data : BitVec 64) (s : State) : Prop :=
  PreRt rt ∧ PreCommon rt stack s ∧
  (z.toNat = 0 → PreNilE R rt stack tab s ∧
    (tab.toNat ≠ 0 → H [descA, tyOf s tab] (s.regs 28).toNat (s.sp.toNat - 80) (rtView R.priv s.mem))) ∧
  (z.toNat ≠ 0 → PreFastE rt stack z tab data fW fP fF fWr s ∧ PreFastX H rt stack z s ∧
    val256 s.mem z.toNat = zv ∧ R2.inv b0 [] (s.regs 28).toNat (view R2.rt [] s.mem) ∧ PreBig R2 b0 rt stack z s)

end Fv256.Arm64.FormatTransfer
