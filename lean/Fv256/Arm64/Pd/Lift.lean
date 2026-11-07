import Fv256.Arm64.LinkEq
import Fv256.Arm64.Pd.Summary

/-!
# `pd_summary` for the consumer's extracted program (arm64)

`pd_summary` is proved once over the library program `Fv256.Arm64.PrettyProg.program` (no `Extracted`); `pd_summary_E` moves it to
an extraction `E` that contains it (`LibIn`, checked by `decide` in the consumer).
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Pd

theorem pd_summary_E (st : Nat) {E : Janus.Program} (hE : Fv256.Arm64.LinkEq.LibIn Fv256.Arm64.PrettyProg.program E)
    (hss : E.contractAddr "runtime.slicebytetostring" = ssAddrL)
    (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract (E.link impl) (E.contractAddr "runtime.slicebytetostring") rt 4096 H (slicebytetostringSpec st)) :
    Summary (E.link impl) pdE
      (fun s => s.regs 0 = z ∧ s.regs 1 = sep ∧ GuardOK s 704 ∧ StackOK s 4608 24 ∧
        E.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 24) rt ∧ Ptr32 s.mem z false ∧
        (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
        (s.mem.readLE z.toNat 32 ≠ 0 →
          H [0, s.sp.toNat - 168 - plen (s.mem.readLE z.toNat 32), plen (s.mem.readLE z.toNat 32)]
            (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt s.mem)) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (prettyBytes (sep.toNat % 256) (val256 s.mem z.toNat)) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])) := by
  have hP := hE.progEq impl
  rw [hss] at hc
  have hc' := Fv256.Arm64.LinkEq.Summary.of_progEq hP.symm hc
  have hsum := Fv256.Arm64.LinkEq.Summary.of_progEq hP (pd_summary st _ rt H z sep hc')
  intro s hpc ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact hsum s hpc ⟨h0, h1, h2, h3, Fv256.Arm64.LinkEq.DataLoaded.of_subset hE.data h4, h5, h6, h7, h8, h9, h10, h11⟩

end Fv256.Arm64.Pd
