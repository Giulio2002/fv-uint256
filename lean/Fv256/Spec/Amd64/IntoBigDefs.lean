import Extracted
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.Core
import Fv256.Spec.C
import Fv256.Spec.Util

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

export Fv256.IntoBig (BigOut BigObj)

/-- The type descriptor of `big.Int` passed to `newobject` (the RIP-relative `LEAQ` at `IntoBig+0x2b`). -/
def bigType : Nat := ripTarget Extracted.program (Extracted.entry + 0x2b)

/-- The type descriptor of `[4]big.Word` (the `LEAQ` at `IntoBig+0xa5`). -/
def arrType : Nat := ripTarget Extracted.program (Extracted.entry + 0xa5)

/-- The address of the write-barrier flag `runtime.writeBarrier` (the `CMPL` at `IntoBig+0x37`). -/
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x37)

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4128) 4152 R.rt ∧ Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4152 ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ b ∧
    Buffer s bp 8 true ∧ Outside bp.toNat 8 R.rt ∧ Janus.Spec.Disjoint bp.toNat 8 ((s.regs 4).toNat - 4128) 4152 ∧
    (z.toNat ≠ 0 →
      Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧ Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4128) 4152 ∧
      Janus.Spec.Disjoint z.toNat 32 bp.toNat 8 ∧
      (s.mem.readLE bp.toNat 8 ≠ 0 →
        Buffer s (BitVec.ofNat 64 (s.mem.readLE bp.toNat 8)) 32 true ∧
        Outside (s.mem.readLE bp.toNat 8) 32 R.rt ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 ((s.regs 4).toNat - 4128) 4152 ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 bp.toNat 8 ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 z.toNat 32 ∧
        (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
          Buffer s (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8)) 32 true ∧
          Outside (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 R.rt ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 4).toNat - 4128) 4152 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 bp.toNat 8 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 z.toNat 32 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.mem.readLE bp.toNat 8) 32)))

/-- Extra separation facts of `correctness`: the goroutine's stack-guard slot is apart from the caller's writable blocks. -/
def PreX (z bp : BitVec 64) (s : State) : Prop :=
  Apart bp.toNat 8 ((s.regs 14).toNat + 16) 8 ∧
    (z.toNat ≠ 0 → s.mem.readLE bp.toNat 8 ≠ 0 →
      s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 < 2 ^ 63 ∧
      Apart (s.mem.readLE bp.toNat 8) 32 ((s.regs 14).toNat + 16) 8 ∧
      (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
        Apart (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 14).toNat + 16) 8))

/-- The postcondition of `correctness`. The return address at `[RSP]` is outside every range, so it is kept. -/
def Post (R : RtInv) (z bp : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, BigOut s'.mem bp.toNat P (val256 s.mem z.toNat)) ∧
  MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
    (bp.toNat, bp.toNat + 8),
    (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)]))

end Fv256.Amd64.IntoBig
