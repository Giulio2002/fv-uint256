import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RecipSpec
import Fv256.CodeIn
import Fv256.RecipProg
import Fv256.Amd64.RecipSummary
import Fv256.Amd64.RecipEnsures

/-!
# `uint256.Reciprocal(m *Int) (mu [5]uint64)` (amd64)

**Documented behaviour.** "Reciprocal computes a 320-bit value representing 1/m", specialised to `m[3] != 0` (so
`2^192 <= m < 2^256`), "returns zero if `m[3] == 0`".  The five result words are returned in the caller's result slot (`RSP+8` on entry).

**Guarantee.** For every `m` with 32 readable bytes (below `2^48`) outside the callee window, and every Go call in which the
stack-growth check falls through, the call returns, and with `M` the number at `m` and `mu` the 320-bit result:
`M < 2^192` gives `mu = 0`; `2^192 <= M` gives `RecipWeak M mu` (`ex-3 <= mu <= ex`, `ex = (2^512-1)/M`); `2^193 <= M` gives
`RecipOK M mu` (`ex-1 <= mu <= ex`).  Nothing outside the frame window changes.

**Proof.** Transfer of the Extracted-free library summary `Fv256.Amd64.RecipSeg.recip_summary` (over `Fv256.RecipProg`; generated segments + the pure-Nat chain `Fv256.F.recip_chain`) by `lib_summary`; `Witness.nonvacuous` below.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Reciprocal

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.RecipProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

theorem correctness (m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [m]
      (fun s => StackGuardOK s 0x1b8 ∧ 0x248 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x240 0x30 ∧ Buffer s m 32 false ∧
        Apart m.toNat 32 ((s.regs regSP).toNat - 0x240) 0x270 ∧
        Apart ((s.regs regG).toNat + 16) 8 ((s.regs regSP).toNat - 0x240) 0x270)
      (fun s s' => (valueAt s m 32 < 2 ^ 192 → s'.mem.readLE ((s.regs regSP).toNat + 8) 40 = 0) ∧
        (2 ^ 192 ≤ valueAt s m 32 → Fv256.F.RecipWeak (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        (2 ^ 193 ≤ valueAt s m 32 → Fv256.F.RecipOK (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 0x240, (s.regs regSP).toNat + 0x30)]) :=
  Fv256.Amd64.RecipEnsures.ensures_recip (Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.RecipSeg.recip_summary) m

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def m : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then m else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0) with rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0x1b8 ∧ 0x248 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x240 0x30 ∧ Buffer s0 m 32 false ∧
    Apart m.toNat 32 ((s0.regs regSP).toNat - 0x240) 0x270 ∧
    Apart ((s0.regs regG).toNat + 16) 8 ((s0.regs regSP).toNat - 0x240) 0x270 :=
  ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    by unfold Apart regSP; decide, by unfold Apart regSP regG; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [m] s ∧
    (StackGuardOK s 0x1b8 ∧ 0x248 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x240 0x30 ∧ Buffer s m 32 false ∧
      Apart m.toNat 32 ((s.regs regSP).toNat - 0x240) 0x270 ∧
      Apart ((s.regs regG).toNat + 16) 8 ((s.regs regSP).toNat - 0x240) 0x270) :=
  ⟨ret, s0, m, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.mem.readLE ((s0.regs regSP).toNat + 8) 40 = 0 := by
  refine (correctness m ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1 ?_⟩
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.Reciprocal
