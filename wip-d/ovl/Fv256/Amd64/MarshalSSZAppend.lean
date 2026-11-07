import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` (amd64) -- PARTIAL: enough capacity

As the arm64 theorem: covers `len + 32 ≤ cap` (the compiled code never reaches `runtime.growslice`); the reallocating case needs a
`growslice` contract for 1-byte elements, which the pinned contract does not provide. Results: `RAX = dp`, `RBX = len + 32`,
`RCX = cap`, nil error in `RDI`, `RSI`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MarshalSSZAppend

set_option maxHeartbeats 16000000 in
theorem correctness (z dp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dp, len, cap]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 112 24 ∧ Buffer s z 32 false ∧
        len.toNat + 32 ≤ cap.toNat ∧ (s.mem.accessible (dp.toNat + len.toNat) 32 true = true ∧ dp.toNat + len.toNat + 32 ≤ 2 ^ 48) ∧
        (z.toNat + 32 ≤ dp.toNat + len.toNat ∨ dp.toNat + len.toNat + 32 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (dp.toNat + len.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat + len.toNat))
      (fun s s' => s'.regs 0 = dp ∧ s'.regs 3 = len + 32#64 ∧ s'.regs 1 = cap ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        s'.mem.readLE (dp.toNat + len.toNat) 32 = valueAt s z 32 ∧
        Janus.MemFrame s.mem s'.mem [(dp.toNat + len.toNat, dp.toNat + len.toNat + 32),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24), ((s.regs regSP).toNat - 112, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, ⟨hzw, hz⟩, hl, ⟨hda, hdb⟩, hd1, hd2, hd3⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hd2 hd3 ⊢
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def dp : BitVec 64 := BitVec.ofNat 64 0x30900

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then dp else if i = 1 then 0 else if i = 7 then 32
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := Fv256.C.bigMem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, 0, 32] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 112 24 ∧ Buffer s0 z 32 false ∧
    (0 : BitVec 64).toNat + 32 ≤ (32 : BitVec 64).toNat ∧
    (s0.mem.accessible (dp.toNat + (0 : BitVec 64).toNat) 32 true = true ∧ dp.toNat + (0 : BitVec 64).toNat + 32 ≤ 2 ^ 48) ∧
    (z.toNat + 32 ≤ dp.toNat + (0 : BitVec 64).toNat ∨ dp.toNat + (0 : BitVec 64).toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 112 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (dp.toNat + (0 : BitVec 64).toNat + 32 ≤ (s0.regs regSP).toNat - 112 ∨ (s0.regs regSP).toNat + 24 ≤ dp.toNat + (0 : BitVec 64).toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, ⟨by decide, by decide⟩, by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 112 24 ∧ Buffer s z 32 false ∧
      len.toNat + 32 ≤ cap.toNat ∧ (s.mem.accessible (dp.toNat + len.toNat) 32 true = true ∧ dp.toNat + len.toNat + 32 ≤ 2 ^ 48) ∧
      (z.toNat + 32 ≤ dp.toNat + len.toNat ∨ dp.toNat + len.toNat + 32 ≤ z.toNat) ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
      (dp.toNat + len.toNat + 32 ≤ (s.regs regSP).toNat - 112 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat + len.toNat)) :=
  ⟨ret, s0, z, dp, 0, 32, hret, setup, hpre⟩

/-- appending to an empty slice of capacity 32: the call returns `(dp, 32, 32)` and a nil error. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = dp ∧ s'.regs 3 = 32 ∧ s'.regs 1 = 32 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 := by
  refine (correctness z dp 0 32 ret hret s0 setup hpre).mono ?_
  intro s' h
  exact ⟨h.1, h.2.1, by rw [h.2.2.1]; decide, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end Witness

end Fv256.Amd64.MarshalSSZAppend
