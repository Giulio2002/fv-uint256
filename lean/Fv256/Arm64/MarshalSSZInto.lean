import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).MarshalSSZInto(dst []byte) ([]byte, error)` (arm64) -- PARTIAL: the success path (`32 ≤ len(dst) ≤ cap(dst)`)

**Scope.** For `len(dst) < 32` the function builds an error with `fmt.Errorf` (left out of the extraction: `--contract fmt.errorf`);
this theorem says nothing about that path (COVERAGE-C.md: partial).

**Guarantee.** For every receiver `z` and slice `dst = (dp, len, cap)` with `32 ≤ len ≤ cap`, 32 readable bytes at `z`, 32 writable bytes at `dp`,
disjoint from each other and from the stack window: the call returns the slice `dst[32:]` = `(dp + (32 if cap > 32 else 0), len - 32, cap - 32)`
and a nil error, the 32 bytes at `dp` are the little-endian encoding of the number at `z` (read before the call), and nothing else
changes except the stack frame.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.MarshalSSZInto

set_option maxHeartbeats 16000000 in
theorem correctness (z dp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dp, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 120 24 ∧ 32 ≤ len.toNat ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
        Ptr32 s.mem z false ∧ Ptr32 s.mem dp true ∧
        Disjoint z.toNat 32 dp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
        Disjoint dp.toNat 32 (s.sp.toNat - 120) 144 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 1 = len - 32#64 ∧
        s'.regs 2 = cap - 32#64 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
        s'.mem.readLE dp.toNat 32 = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), (s.sp.toNat + 8, s.sp.toNat + 24), (s.sp.toNat - 120, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hl, hlc, hc48, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3
  janus_run
  refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), ?_, ?_, ?_⟩
  · rw [Fv256.C.mask32 cap (by omega) hc48]
  · simp only [val256, Util.readLE_32]
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
  { regs := fun i => if i = 0 then z else if i = 1 then dp else if i = 2 then 40 else if i = 3 then 64
      else if i = 28 then BitVec.ofNat 64 wg else if i = 29 then BitVec.ofNat 64 wsp - 8#64
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Fv256.C.bigMem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, 40, 64] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 120 24 ∧ 32 ≤ (40 : BitVec 64).toNat ∧ (40 : BitVec 64).toNat ≤ (64 : BitVec 64).toNat ∧
    (64 : BitVec 64).toNat < 2 ^ 48 ∧ Ptr32 s0.mem z false ∧ Ptr32 s0.mem dp true ∧
    Disjoint z.toNat 32 dp.toNat 32 ∧ Disjoint z.toNat 32 (s0.sp.toNat - 120) 144 ∧
    Disjoint dp.toNat 32 (s0.sp.toNat - 120) 144 ∧ s0.regs 29 = s0.sp - 8#64 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, rfl⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s 120 24 ∧ 32 ≤ len.toNat ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
      Ptr32 s.mem z false ∧ Ptr32 s.mem dp true ∧
      Disjoint z.toNat 32 dp.toNat 32 ∧ Disjoint z.toNat 32 (s.sp.toNat - 120) 144 ∧
      Disjoint dp.toNat 32 (s.sp.toNat - 120) 144 ∧ s.regs 29 = s.sp - 8#64) :=
  ⟨ret, s0, z, dp, 40, 64, hret, setup, hpre⟩

/-- with `len = 40`, `cap = 64`: the call returns `dst[32:] = (dp + 32, 8, 32)` and a nil error. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = dp + 32 ∧ s'.regs 1 = 8 ∧ s'.regs 2 = 32 ∧ s'.regs 3 = 0 ∧ s'.regs 4 = 0 := by
  refine (correctness z dp 40 64 ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_, ?_, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · rw [h.2.1]; decide
  · rw [h.2.2.1]; decide
  · rw [h.2.2.2.1]; decide

end Witness

end Fv256.Arm64.MarshalSSZInto
