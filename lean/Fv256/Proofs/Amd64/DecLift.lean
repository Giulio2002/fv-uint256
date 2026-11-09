import Fv256.Proofs.Common.LinkEq
import Fv256.Proofs.Amd64.DecSummary

/-!
# `dec_summary` for a consumer's extracted program

`Fv256.Amd64.Dec.dec_summary` is proved once, over the library program `Fv256.DecProg.program`, in modules that do not
import `Extracted`.  `dec_summary_E` moves it to a consumer's extracted program `E` (any extraction that contains the library
segments; `LibIn` is checked by `decide` in the consumer): the runtime-contract hypothesis `hc` is about `E.link impl`
(the real program), and is moved to the library program linked with the consumer's remaining code and `impl`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.Dec

theorem dec_summary_E (st : Nat) {E : Janus.Amd64.Program} (hE : Fv256.LinkEq.LibIn Fv256.DecProg.program E)
    (hss : E.contractAddr "runtime.slicebytetostring" = ssAddrL)
    (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (E.link impl) (E.contractAddr "runtime.slicebytetostring") rt 4096 H (slicebytetostringSpec st)) :
    Summary (E.link impl) decE
      (fun s => s.regs 0 = z ∧ StackGuardOK s 0x378 ∧ StackWritable s 4568 8 ∧ E.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4568) (4568 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4568 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 384 - 0x58) (rtView rt s.mem)) ∧
        s.xmm 15 = 0 ∧ s.df = false ∧ s.mem.readLE (s.regs 4).toNat 8 < 140737488355328)
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧ s'.xmm 15 = s.xmm 15 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)]) ∧
        Fv256.E.DecAt rt 5163273 5176582 5134938 (s'.regs 0).toNat (s'.regs 3).toNat ∧
        (valueAt s z 32 < 100 → MemFrame s.mem s'.mem [((s.regs 4).toNat - 4568, (s.regs 4).toNat + 8)])) := by
  have hP := hE.progEq impl
  rw [hss] at hc
  have hc' := Fv256.LinkEq.Summary.of_progEq hP.symm hc
  have hsum := Fv256.LinkEq.Summary.of_progEq hP (dec_summary st _ rt H z hc')
  intro s hpc ⟨h0, h1, h2, h3, h4⟩
  exact hsum s hpc ⟨h0, h1, h2, Fv256.LinkEq.DataLoaded.of_subset hE.data h3, h4⟩

end Fv256.Amd64.Dec
