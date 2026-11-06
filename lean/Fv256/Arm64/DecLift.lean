import Fv256.Arm64.LinkEq
import Fv256.Arm64.DecSummary

/-! `dec_summary` (proved once over `Fv256.Arm64.DecProg.program`, `Extracted`-free) for a consumer's extracted program `E`
that contains the library (`LibIn`, checked by `decide` in the consumer). -/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.Dec

theorem dec_summary_E (st : Nat) {E : Janus.Program} (hE : Fv256.Arm64.LinkEq.LibIn Fv256.Arm64.DecProg.program E)
    (hss : E.contractAddr "runtime.slicebytetostring" = ssAddrL)
    (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (E.link impl) (E.contractAddr "runtime.slicebytetostring") rt 4096 H (slicebytetostringSpec st)) :
    Summary (E.link impl) decE
      (fun s => s.regs 0 = z ∧ GuardOK s 688 ∧ StackOK s 4608 8 ∧ E.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem)) ∧
        (s.regs 30).toNat < 2 ^ 48 ∧ (s.regs 30).toNat % 4 = 0)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8)]) ∧
        Fv256.E.DecAt rt 989280 1002589 960826 (s'.regs 0).toNat (s'.regs 1).toNat) := by
  have hP := hE.progEq impl
  rw [hss] at hc
  have hc' := Fv256.Arm64.LinkEq.Summary.of_progEq hP.symm hc
  have hsum := Fv256.Arm64.LinkEq.Summary.of_progEq hP (dec_summary st _ rt H z hc')
  intro s hpc ⟨h0, h1, h2, h3, h4⟩
  exact hsum s hpc ⟨h0, h1, h2, Fv256.Arm64.LinkEq.DataLoaded.of_subset hE.data h3, h4⟩

end Fv256.Arm64.Dec
