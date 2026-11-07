import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).MarshalSSZInto(dst []byte) ([]byte, error)` (amd64) -- PARTIAL: the success path (`32 ≤ len(dst) ≤ cap(dst)`)

As the arm64 theorem. Results: `RAX = dp + (32 if cap > 32 else 0)`, `RBX = len - 32`, `RCX = cap - 32`, nil error in `RDI`, `RSI`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MarshalSSZInto

set_option maxHeartbeats 16000000 in
theorem correctness (z dp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, dp, len, cap]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ 32 ≤ len.toNat ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
        Buffer s z 32 false ∧ Buffer s dp 32 true ∧
        (z.toNat + 32 ≤ dp.toNat ∨ dp.toNat + 32 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (dp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat))
      (fun s s' => s'.regs 0 = dp + (if 32 < cap.toNat then 32#64 else 0#64) ∧ s'.regs 3 = len - 32#64 ∧
        s'.regs 1 = cap - 32#64 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        s'.mem.readLE dp.toNat 32 = valueAt s z 32 ∧
        Janus.MemFrame s.mem s'.mem [(dp.toNat, dp.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
          ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hl, hlc, hc48, ⟨hzw, hz⟩, ⟨hdw, hd⟩, hd1, hd2, hd3⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hd2 hd3 ⊢
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · rw [Fv256.C.mask32b cap (by omega) hc48, BitVec.add_comm]
  · janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def bp : BitVec 64 := BitVec.ofNat 64 0x30900

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then bp else if i = 1 then 40 else if i = 7 then 64
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := Fv256.C.bigMem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, bp, 40, 64] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 96 24 ∧ 32 ≤ (40 : BitVec 64).toNat ∧ (40 : BitVec 64).toNat ≤ (64 : BitVec 64).toNat ∧
    (64 : BitVec 64).toNat < 2 ^ 48 ∧ Buffer s0 z 32 false ∧ Buffer s0 bp 32 true ∧
    (z.toNat + 32 ≤ bp.toNat ∨ bp.toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 96 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (bp.toNat + 32 ≤ (s0.regs regSP).toNat - 96 ∨ (s0.regs regSP).toNat + 24 ≤ bp.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z dp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ 32 ≤ len.toNat ∧ len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 48 ∧
      Buffer s z 32 false ∧ Buffer s dp 32 true ∧
      (z.toNat + 32 ≤ dp.toNat ∨ dp.toNat + 32 ≤ z.toNat) ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
      (dp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ dp.toNat)) :=
  ⟨ret, s0, z, bp, 40, 64, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = bp + 32 ∧ s'.regs 3 = 8 ∧ s'.regs 1 = 32 ∧ s'.regs 7 = 0 ∧ s'.regs 6 = 0 := by
  refine (correctness z bp 40 64 ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_, ?_, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  · rw [h.2.1]; decide
  · rw [h.2.2.1]; decide
  · rw [h.2.2.2.1]; decide

end Witness

end Fv256.Amd64.MarshalSSZInto
