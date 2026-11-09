import Extracted
import Fv256.Spec.C
import Fv256.Spec.Core
import Fv256.Spec.IntoBigCommon
import Fv256.Spec.Util

/-! SPECIFICATION part (generated): the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

export Fv256.IntoBig (BigOut BigObj)

def nm : String := "github.com/holiman/uint256.(*Int).IntoBig"

/-- The type descriptor of `big.Int` passed to `newobject` (`ADRP`+`ADD` at `IntoBig+0x2c`). -/
def bigType : Nat :=
  adrpLdTarget ((Extracted.entry + 0x60) + 0x2c) (segWord Extracted.program nm 11) (segWord Extracted.program nm 12) 0

/-- The type descriptor of `[4]big.Word` (`ADRP`+`ADD` at `IntoBig+0xa0`). -/
def arrType : Nat :=
  adrpLdTarget ((Extracted.entry + 0x60) + 0xa0) (segWord Extracted.program nm 40) (segWord Extracted.program nm 41) 0

/-- The address of the write-barrier flag `runtime.writeBarrier` (`ADRP`+`LDR W` at `IntoBig+0x38`). -/
def flagAddr : Nat :=
  adrpLdTarget ((Extracted.entry + 0x60) + 0x38) (segWord Extracted.program nm 14) (segWord Extracted.program nm 15) 2

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  GuardOK s 4144 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4144) 4168 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168 ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ b ∧
    Ptr s.mem bp 8 true ∧ Outside bp.toNat 8 R.rt ∧ Disjoint bp.toNat 8 (s.sp.toNat - 4144) 4168 ∧
    (z.toNat ≠ 0 →
      Ptr s.mem z 32 false ∧ Outside z.toNat 32 R.rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
      Disjoint z.toNat 32 bp.toNat 8 ∧
      (s.mem.readLE bp.toNat 8 ≠ 0 →
        Ptr s.mem (BitVec.ofNat 64 (s.mem.readLE bp.toNat 8)) 32 true ∧
        Outside (s.mem.readLE bp.toNat 8) 32 R.rt ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 (s.sp.toNat - 4144) 4168 ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 bp.toNat 8 ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 z.toNat 32 ∧
        (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
          Ptr s.mem (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8)) 32 true ∧
          Outside (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 R.rt ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.sp.toNat - 4144) 4168 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 bp.toNat 8 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 z.toNat 32 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.mem.readLE bp.toNat 8) 32)))

/-- Extra separation facts of `correctness`: the stack-guard slot `g + 16` is apart from the caller's writable blocks. -/
def PreX (z bp : BitVec 64) (s : State) : Prop :=
  Apart bp.toNat 8 ((s.regs 28).toNat + 16) 8 ∧
    (z.toNat ≠ 0 → s.mem.readLE bp.toNat 8 ≠ 0 →
      s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 < 2 ^ 63 ∧
      Apart (s.mem.readLE bp.toNat 8) 32 ((s.regs 28).toNat + 16) 8 ∧
      (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
        Apart (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 28).toNat + 16) 8))

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (z bp : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, BigOut s'.mem bp.toNat P (val256 s.mem z.toNat)) ∧
  MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
    (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))

end Fv256.Arm64.IntoBig

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
