import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `uint256.NewInt(val uint64) *Int` (arm64)

**Guarantee.** For every `val` (`X0`), every list `rt` of runtime-owned memory ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract`, `Janus/Contracts/Alloc.lean`; hypothesis `hnew`),
and every Go call whose stack-growth check falls through (`GuardOK s 0`, the stack window `[SP-4144, SP+24)` (NewInt's frame, 4096 bytes for the runtime, spill slots) writable and aligned (`StackOK s 4144 24`)) outside `rt`, with the read-only data (the type descriptor of `Int`) loaded,
the call returns, obeys the ABI, and the result is a pointer `ptr`
with `[ptr, ptr+32)` inside the runtime-owned ranges (a *fresh* object, disjoint from everything the caller holds), writable and
16-byte aligned, whose 32 bytes hold `Fv256.Spec.setU val` (the number `val`; the allocator returns zeroed memory), and memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted: `janus extract --contract
runtime.newobject`); see `docs/RUNTIME-CONTRACTS.md` of Janus.

**Non-vacuity.** The contract hypothesis is satisfiable (Janus: `Janus.Contracts.newobject_satisfiable`); the remaining
preconditions are linear facts about the pointers, `rt` and the stack window. No concrete `Witness` state is built for this theorem
(it would need a model of the runtime heap at the linked address); see `COVERAGE.md`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.NewInt

/-- The address of `uint256.Int`'s type descriptor, the argument `NewInt` passes to `runtime.newobject`
(the `ADRP` + `ADD` pair at `NewInt+0x1c`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.NewInt" 7)
    (segWord Extracted.program "github.com/holiman/uint256.NewInt" 8) 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (val : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [val]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = Spec.setU val.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  janus_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · have hzb := ‹ZeroBytes _ _ 32›
    have z8 := hzb.readLE (k := 8) (j := 8) (by omega)
    have z16 := hzb.readLE (k := 16) (j := 8) (by omega)
    have z24 := hzb.readLE (k := 24) (j := 8) (by omega)
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
    rw [z8, z16, z24]
    have := val.isLt
    simp only [Spec.setU]
    omega
  · janus_frame

end Fv256.Arm64.NewInt
