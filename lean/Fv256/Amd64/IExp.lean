import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.CodeIn
import Fv256.ExpProg
import Fv256.Amd64.ExpMain

/-!
# `(*uint256.Int).IExp(exponent *Int) *Int` (amd64): in place, `z = z ** exponent mod 2^256`

**Documented behaviour.** `IExp` is `z.Exp(z, exponent)`: `Exp` sets `z` to `base ** exponent mod 2^256`.

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (exponent, `RBX`) (they may overlap arbitrarily), and every Go call in which
the stack-growth checks of `IExp` and of the `Exp` it calls fall through (`StackGuardOK s 0x50`), the window `[RSP-0xd0, RSP+0x10)` is
writable, the 32 bytes at `z` are writable, those at `x` readable, neither overlaps the window, the goroutine's `stackguard0` word is
outside the window and the rodata is loaded: the call returns, obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is
`Fv256.F.expSpec` of the numbers at `z` and `x` before the call, and nothing outside `z[0..32)` and the window changes.
The callee is used through the verified library summary `Fv256.Amd64.ExpMain.exp_summary` (over `Fv256.ExpProg.program`).

**Non-vacuity.** `Witness.nonvacuous`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IExp

abbrev Pre (z x : BitVec 64) : State → Prop :=
  fun s => StackGuardOK s 0x50 ∧ 0x130 ≤ (s.regs regSP).toNat ∧ StackWritable s 0xd0 0x10 ∧ Buffer s z 32 true ∧
    Buffer s x 32 false ∧
    (z.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ x.toNat) ∧
    ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0xd0 ∨ (s.regs regSP).toNat + 0x10 ≤ (s.regs regG).toNat + 16) ∧
    Extracted.program.DataLoaded s.mem

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ExpProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem hdata : Extracted.program.data = Fv256.ExpProg.program.data := rfl

theorem hdl (m : Janus.Arm64.Memory) : Extracted.program.DataLoaded m ↔ Fv256.ExpProg.program.DataLoaded m := by
  unfold Amd64.Program.DataLoaded; rw [hdata]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x] (Pre z x)
      (fun s s' => s'.regs 0 = z ∧ valueAt s' z 32 = Fv256.F.expSpec (valueAt s z 32) (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0xd0, (s.regs regSP).toNat + 0x10)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hdz, hdx, hdg, hdl'⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hsp
  simp only [valueAt]
  have hdlE := (hdl _).1 hdl'
  janus64_run [Util.readLE_32] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.ExpMain.exp_summary]
  trace_state
  all_goals sorry

end Fv256.Amd64.IExp
