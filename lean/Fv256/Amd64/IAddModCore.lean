import Extracted
import Fv256.Spec
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.AddModProg
import Fv256.Amd64.AddModSpecS

/-!
# `(*uint256.Int).IAddMod(x, m *Int) *Int` (amd64): in place, `z = (z + x) mod m`   (core: conditional on the callee summary)

`IAddMod` is `z.AddMod(z, x, m)`; the callee is used through the library summary `Fv256.Amd64.AddModSum.addmod_summary`
over `Fv256.AddModProg.program`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.IAddModCore

/-- entry of `(*Int).AddMod` in the library program -/
abbrev addEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

abbrev Pre (z x m : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x330 ∧ 0x3b0 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x10 ∧ Buffer s z 32 true ∧
    Buffer s x 32 false ∧ Buffer s m 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ m.toNat) ∧
    (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
    (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x378 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
    ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16) ∧
    Extracted.program.DataLoaded s.mem

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.AddModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.AddModProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.AddModProg.program.DataLoaded m := by
  unfold Amd64.Program.DataLoaded; rw [hdata]

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness (hS : Summary Fv256.AddModProg.program addEntry (fun s => AddPre Fv256.AddModProg.program s) AddPost)
    (z x m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, m] (Pre z x m)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.addmodSpec (valueAt s z 32) (valueAt s x 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, hdz, hdx, hdm, hzm, hzx, hdg, hdgz, hdlE⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdgz
  simp only [regSP] at hacc hlow hnw hdz hdx hdm hsp
  simp only [valueAt]
  have hdlA : Fv256.AddModProg.program.DataLoaded s.mem := (hdl _).1 hdlE
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcLib hS]
  trace_state
  all_goals sorry

end Fv256.Amd64.IAddModCore
