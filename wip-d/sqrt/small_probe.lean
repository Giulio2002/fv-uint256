import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.SqrtMath
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Sqrt

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x200 ∧ 0x280 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x1f0 0x20 ∧ s.xmm 15 = 0 ∧
    Buffer s z 32 true ∧ Buffer s x 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ x.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x1f0 ∨ (s.regs regSP).toNat + 0x20 ≤ (s.regs regG).toNat + 16)

set_option maxHeartbeats 8000000 in
theorem small (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Pre z x s ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0)
      (fun s s' => s'.regs 0 = z ∧ Fv256.F.IsSqrt (valueAt s x 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x1f0, (s.regs regSP).toNat + 0x20)]) := by
  intro ret hret s hs ⟨⟨hg, hsp, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hzx, hdg⟩, h1, h2, h3⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  simp only [valueAt]
  janus64_run [Util.readLE_32, Fv256.B.or3_zero_iff, h1, h2, h3] until [Extracted.entry + 0x312]
  trace_state
  all_goals sorry

end Fv256.Amd64.Sqrt
