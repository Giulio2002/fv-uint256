import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Clone() *Int` (arm64)

**Guarantee.** For every receiver `z` (`X0`), every list `rt` of runtime-owned memory ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract`, `Janus/Contracts/Alloc.lean`; hypothesis `hnew`),
and every Go call whose stack-growth check falls through (`GuardOK s 0`, the stack window `[SP-4144, SP+24)` (Clone's frame, 4096 bytes for the runtime, spill slots) writable and aligned (`StackOK s 4144 24`)) outside `rt`, with the read-only data (the type descriptor of `Int`) loaded,
the 32 bytes at `z` readable, outside `rt` and outside the stack window: the call returns, obeys the ABI, and the result is a pointer `ptr`
with `[ptr, ptr+32)` inside the runtime-owned ranges (a *fresh* object, disjoint from everything the caller holds), writable and
16-byte aligned, whose 32 bytes are the number at `z` (read before the call), and memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted: `janus extract --contract
runtime.newobject`); see `docs/RUNTIME-CONTRACTS.md` of Janus.

**Non-vacuity.** The contract hypothesis is satisfiable (Janus: `Janus.Contracts.newobject_satisfiable`); the remaining
preconditions are linear facts about the pointers, `rt` and the stack window. No concrete `Witness` state is built for this theorem
(it would need a model of the runtime heap at the linked address); see `COVERAGE.md`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.Clone

/-- The address of `uint256.Int`'s type descriptor, the argument `Clone` passes to `runtime.newobject`
(the `ADRP` + `ADD` pair at `Clone+0x1c`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x1c) (segWord Extracted.program "github.com/holiman/uint256.(*Int).Clone" 7)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).Clone" 8) 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  have hdz := InRanges.disjoint ‹InRanges _ 32 rt› hzo
  janus_run
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Util.readLE8_mod, Nat.reducePow]
  · janus_frame

end Fv256.Arm64.Clone
