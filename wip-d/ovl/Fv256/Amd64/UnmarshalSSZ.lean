import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).UnmarshalSSZ(buf []byte) error` (amd64) -- PARTIAL: the success path (`len(buf) = 32`)

As the arm64 theorem (error path through `fmt.errorf` not covered, see COVERAGE-C.md). The error is returned in `RAX`, `RBX`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.UnmarshalSSZ

set_option maxHeartbeats 16000000 in
theorem correctness (z bp len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, bp, len, cap]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ len.toNat = 32 ∧ Buffer s z 32 true ∧ Buffer s bp 32 false ∧
        (z.toNat + 32 ≤ bp.toNat ∨ bp.toNat + 32 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (bp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ bp.toNat))
      (fun s s' => s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.mem.readLE z.toNat 32 = s.mem.readLE bp.toNat 32 ∧
        Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 24),
          ((s.regs regSP).toNat - 96, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hl, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hd2 hd3 ⊢
  janus64_run [Util.readLE_32]
  janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def bp : BitVec 64 := BitVec.ofNat 64 0x30900

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then bp else if i = 1 then 32 else if i = 7 then 32
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := Fv256.C.bigMem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, bp, 32, 32] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 96 24 ∧ (32 : BitVec 64).toNat = 32 ∧ Buffer s0 z 32 true ∧ Buffer s0 bp 32 false ∧
    (z.toNat + 32 ≤ bp.toNat ∨ bp.toNat + 32 ≤ z.toNat) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 96 ∨ (s0.regs regSP).toNat + 24 ≤ z.toNat) ∧
    (bp.toNat + 32 ≤ (s0.regs regSP).toNat - 96 ∨ (s0.regs regSP).toNat + 24 ≤ bp.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z bp len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, bp, len, cap] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 96 24 ∧ len.toNat = 32 ∧ Buffer s z 32 true ∧ Buffer s bp 32 false ∧
      (z.toNat + 32 ≤ bp.toNat ∨ bp.toNat + 32 ≤ z.toNat) ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
      (bp.toNat + 32 ≤ (s.regs regSP).toNat - 96 ∨ (s.regs regSP).toNat + 24 ≤ bp.toNat)) :=
  ⟨ret, s0, z, bp, 32, 32, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ s'.mem.readLE z.toNat 32 = s0.mem.readLE bp.toNat 32 :=
  (fun h => h.mono fun s' h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) (correctness z bp 32 32 ret hret s0 setup hpre)

end Witness

end Fv256.Amd64.UnmarshalSSZ
