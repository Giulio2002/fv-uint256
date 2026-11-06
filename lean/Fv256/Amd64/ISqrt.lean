import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.SqrtProg
import Fv256.Amd64.SqrtSummaryL
import Fv256.SqrtTac

/-!
# `(*uint256.Int).ISqrt() *Int` (amd64): in place, `z = ⌊√z⌋`

**Documented behaviour.** `ISqrt` is `z.Sqrt(z)`.

**Guarantee.** For every pointer `z` (receiver, `RAX`) and every Go call in which the stack-growth checks of `ISqrt` and of the `Sqrt` it calls
fall through (`StackGuardOK s 0x220`), the window `[RSP-0x210, RSP+0x10)` is writable, the 32 bytes at `z` are writable, `z` does not overlap the window
and `stackguard0` is outside it: the call returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `⌊√⌋` of the number at `z`
before the call (`Fv256.F.IsSqrt`), and nothing outside `z[0..32)` and the window changes. The callee is used through the library summary
`Fv256.Amd64.SqrtLib.sqrt_summary` over `Fv256.SqrtProg.program`.

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ISqrt

abbrev Pre (z : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x220 ∧ 0x2a0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x210 0x10 ∧ Buffer s z 32 true ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x210 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16)

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.SqrtProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z] (Pre z)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (valueAt s z 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x210, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hdz, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.SqrtLib.sqrt_summary]
  grab_const Fv256.F.IsSqrt as hsq
  grab_const Janus.MemFrame as hf
  refine ⟨hsq, MemFrame.trans (rs := [(z.toNat, z.toNat + 32), ((s.regs 4).toNat - 0x210, (s.regs 4).toNat + 0x10)])
    (rs'' := [(z.toNat, z.toNat + 32), ((s.regs 4).toNat - 0x210, (s.regs 4).toNat + 0x10)]) ?A hf ?sub⟩
  · repeat' (first | exact MemFrame.refl _ _ | refine MemFrame.writeLE_inRanges ?_ _ ⟨((s.regs 4).toNat - 0x210, (s.regs 4).toNat + 0x10), List.mem_cons_of_mem _ (List.mem_cons_self ..), by omega, by omega⟩)
  · intro a n h; simp [Outside] at h ⊢; omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : Pre z s0 :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold regSP; decide, by unfold regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧ Pre z s :=
  ⟨ret, s0, z, hret, setup, hpre⟩

end Witness

end Fv256.Amd64.ISqrt
