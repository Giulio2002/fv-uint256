import Fv256.LinkEq
import Fv256.Amd64.Pd.Summary

/-!
# `pd_summary` for the consumer's extracted program

`pd_summary` is proved once over the library program `Fv256.PrettyProg.program` (no `Extracted`); `pd_summary_E` moves it to
an extraction `E` that contains it (`LibIn`, checked by `decide` in the consumer).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Pd

theorem pd_summary_E (st : Nat) {E : Janus.Amd64.Program} (hE : Fv256.LinkEq.LibIn Fv256.PrettyProg.program E)
    (hss : E.contractAddr "runtime.slicebytetostring" = ssAddrL)
    (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract64 (E.link impl) (E.contractAddr "runtime.slicebytetostring") rt 4096 H (slicebytetostringSpec st)) :
    Summary (E.link impl) pdE
      (fun s => s.regs 0 = z ∧ s.regs 3 = sep ∧ StackGuardOK s 0x378 ∧ StackWritable s 4576 0x18 ∧
        E.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4576) (4576 + 0x18) rt ∧ (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16) ∧
        (s.mem.readLE z.toNat 32 ≠ 0 →
          H [0, (s.regs 4).toNat - 0xa8 - plen (s.mem.readLE z.toNat 32), plen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x188) (rtView rt s.mem)) ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 140737488355328)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (prettyBytes (sep.toNat % 256) (valueAt s z 32)) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])) := by
  have hP := hE.progEq impl
  rw [hss] at hc
  have hc' := Fv256.LinkEq.Summary.of_progEq hP.symm hc
  have hsum := Fv256.LinkEq.Summary.of_progEq hP (pd_summary st _ rt H z sep hc')
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  exact hsum s hpc ⟨h0, h1, h2, h3, Fv256.LinkEq.DataLoaded.of_subset hE.data h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Fv256.Amd64.Pd
