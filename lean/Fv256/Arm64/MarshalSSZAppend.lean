import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` (arm64) -- PARTIAL: enough capacity

**Scope.** The theorem covers calls where `dst` already has room for 32 more bytes (`len + 32 ≤ cap`), which is the case in which the
compiled code never calls `runtime.growslice`. For `len + 32 > cap` the function reallocates through `runtime.growslice` with a
1-byte element type, which the pinned `GrowsliceContract` does not cover (it is stated for 8-byte pointer-free elements only);
that case is NOT verified (see COVERAGE-C.md).

**Guarantee.** For every receiver `z` and slice `dst = (dp, len, cap)` with `len + 32 ≤ cap`, `[dp+len, dp+len+32)` writable and
disjoint from the 32 bytes at `z` and from the stack window: the call returns the slice `(dp, len+32, cap)` and a nil error, the 32 bytes
written at `dp + len` are the little-endian encoding of the number at `z`, and nothing else changes except the stack frame.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MarshalSSZAppend

set_option maxHeartbeats 16000000 in
theorem correctness (z dp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dp, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 136 24 ∧ Ptr32 s.mem z false ∧
        len.toNat + 32 ≤ cap.toNat ∧ (s.mem.accessible (dp.toNat + len.toNat) 32 true = true ∧ dp.toNat + len.toNat + 32 ≤ 2 ^ 48) ∧
        Disjoint z.toNat 32 (dp.toNat + len.toNat) 32 ∧
        Disjoint z.toNat 32 (s.sp.toNat - 136) 160 ∧ Disjoint (dp.toNat + len.toNat) 32 (s.sp.toNat - 136) 160 ∧
        s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.regs 0 = dp ∧ s'.regs 1 = len + 32#64 ∧ s'.regs 2 = cap ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
        s'.mem.readLE (dp.toNat + len.toNat) 32 = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem [((dp.toNat + len.toNat), (dp.toNat + len.toNat) + 32), (s.sp.toNat + 8, s.sp.toNat + 24),
          (s.sp.toNat - 136, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, hl, ⟨hda, hdb⟩, hd1, hd2, hd3, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3
  janus_run
  refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), ?_, ?_⟩
  · simp only [val256, Util.readLE_32, Nat.add_assoc]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
      Util.readLE8_mod, Nat.reducePow]
  · janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def dp : BitVec 64 := BitVec.ofNat 64 0x30900

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then dp else if i = 2 then 0 else if i = 3 then 32
      else if i = 28 then BitVec.ofNat 64 wg else if i = 29 then BitVec.ofNat 64 wsp - 8#64
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Fv256.C.bigMem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, 0, 32] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 136 24 ∧ Ptr32 s0.mem z false ∧
    (0 : BitVec 64).toNat + 32 ≤ (32 : BitVec 64).toNat ∧
    (s0.mem.accessible (dp.toNat + (0 : BitVec 64).toNat) 32 true = true ∧ dp.toNat + (0 : BitVec 64).toNat + 32 ≤ 2 ^ 48) ∧
    Disjoint z.toNat 32 (dp.toNat + (0 : BitVec 64).toNat) 32 ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 136) 160 ∧ Disjoint (dp.toNat + (0 : BitVec 64).toNat) 32 (s0.sp.toNat - 136) 160 ∧
    s0.regs 29 = s0.sp - 8#64 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide,
    ⟨by decide, by decide⟩, ?_, ?_, ?_, rfl⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s 136 24 ∧ Ptr32 s.mem z false ∧
      len.toNat + 32 ≤ cap.toNat ∧ (s.mem.accessible (dp.toNat + len.toNat) 32 true = true ∧ dp.toNat + len.toNat + 32 ≤ 2 ^ 48) ∧
      Disjoint z.toNat 32 (dp.toNat + len.toNat) 32 ∧
      Disjoint z.toNat 32 (s.sp.toNat - 136) 160 ∧ Disjoint (dp.toNat + len.toNat) 32 (s.sp.toNat - 136) 160 ∧
      s.regs 29 = s.sp - 8#64) :=
  ⟨ret, s0, z, dp, 0, 32, hret, setup, hpre⟩

/-- appending to an empty slice of capacity 32: the call returns `(dp, 32, 32)` and a nil error. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = dp ∧ s'.regs 1 = 32 ∧ s'.regs 2 = 32 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 := by
  refine (correctness z dp 0 32 ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, h.2.1, by rw [h.2.2.1]; decide, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Witness

end Fv256.Arm64.MarshalSSZAppend
