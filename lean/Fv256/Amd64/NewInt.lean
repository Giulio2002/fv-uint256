import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `uint256.NewInt(val uint64) *Int` (amd64)

**Guarantee.** For every `val` (`RAX`), every list `rt` of runtime-owned memory ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract64`, `Janus/Contracts/AllocAmd64.lean`; hypothesis `hnew`),
and every Go call whose stack-growth check falls through (`StackGuardOK s 0`, the stack window `[RSP-4128, RSP+24)` writable (`StackWritable s 4128 24`)) outside `rt`, with the read-only data (the type descriptor of `Int`) loaded,
the call returns, obeys the ABI, and the result is a pointer `ptr`
with `[ptr, ptr+32)` inside the runtime-owned ranges (a *fresh* object, disjoint from everything the caller holds), writable and
16-byte aligned, whose 32 bytes hold `Fv256.Spec.setU val` (the number `val`; the allocator returns zeroed memory), and memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted: `janus extract --contract
runtime.newobject`); see `docs/RUNTIME-CONTRACTS.md` of Janus.

**Non-vacuity.** The contract hypothesis is satisfiable (Janus: `Janus.Contracts.newobject64_satisfiable`); the remaining
preconditions are linear facts about the pointers, `rt` and the stack window. No concrete `Witness` state is built for this theorem
(it would need a model of the runtime heap at the linked address); see `COVERAGE.md`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.NewInt

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (val : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [val]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4128 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4128) 4152 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 32) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
        s'.mem.accessible ptr 32 true = true ∧
        s'.mem.readLE ptr 32 = Spec.setU val.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x1f] calls [hnew.pos]
  have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
  janus64_run [Util.readLE_32]
  refine ⟨_, rfl, ‹_›, ‹_›, ‹_›, ?_, ?_⟩
  · have hzb := ‹ZeroBytes _ _ 32›
    have z8 := hzb.readLE (k := 8) (j := 8) (by omega)
    have z16 := hzb.readLE (k := 16) (j := 8) (by omega)
    have z24 := hzb.readLE (k := 24) (j := 8) (by omega)
    try simp only [Util.readLE_32]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
    rw [z8, z16, z24]
    have := val.isLt
    simp only [Spec.setU]
    omega
  · janus_frame

end Fv256.Amd64.NewInt
