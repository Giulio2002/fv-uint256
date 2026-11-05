import Extracted
import Fv256.Arm64.UdivremE
import Fv256.Arm64.UdivremF
import Fv256.Arm64.KnuthSummary

/-!
# arm64 `udivrem`: unconditional entries (hKn discharged by `Fv256.Arm64.KnuthSummary.knuth_summary`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremF Fv256.Arm64.UdivremFront Fv256.Arm64.UdivremE

namespace Fv256.Arm64.UdivremFinal

theorem udivrem_summary_L_final {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) :
    Summary Extracted.program ku
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 304 ∧ StackOK s 344 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 1).toNat = L ∧ (s.regs 4).toNat = L ∧
        (s.regs 0).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * L) true = true ∧
        (s.regs 3).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * L) false = true ∧
        (s.regs 6).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat 32 false = true ∧
        ((s.regs 0).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        Fv256.B.wv s.mem (s.regs 6).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧
        ((s.regs 7).toNat ≠ 0 → (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 7).toNat 32 true = true ∧
          Fv256.B.wv s.mem (s.regs 7).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 3).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 3).toNat) ∧
          ((s.regs 7).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 7).toNat)))
      (UPost L) :=
  Fv256.Arm64.UdivremE.udivrem_summary_L hL4 hL8 Fv256.Arm64.KnuthSummary.knuth_summary

theorem udivrem_nil_L_final {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) :
    Summary Extracted.program ku
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 304 ∧ StackOK s 344 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 1).toNat = L ∧ (s.regs 4).toNat = L ∧
        (s.regs 0).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * L) true = true ∧
        (s.regs 3).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * L) false = true ∧
        (s.regs 6).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat 32 false = true ∧
        ((s.regs 0).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        Fv256.B.wv s.mem (s.regs 6).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧ (s.regs 7).toNat = 0)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        Fv256.B.wv s'.mem (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 3).toNat L / Fv256.B.wv s.mem (s.regs 6).toNat 4 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L), (s.sp.toNat - 344, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 72)]) :=
  Fv256.Arm64.UdivremF.udivrem_nil_L hL4 hL8 Fv256.Arm64.KnuthSummary.knuth_summary

theorem udivrem_rem_L_final {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) :
    Summary Extracted.program ku
      (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 304 ∧ StackOK s 344 72 ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 28).toNat + 16) ∧
        (s.regs 1).toNat = L ∧ (s.regs 4).toNat = L ∧
        (s.regs 0).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat (8 * L) true = true ∧
        (s.regs 3).toNat + 8 * L ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat (8 * L) false = true ∧
        (s.regs 6).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 6).toNat 32 false = true ∧
        ((s.regs 0).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 8 * L ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 3).toNat) ∧
        ((s.regs 6).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 6).toNat) ∧
        Fv256.B.wv s.mem (s.regs 6).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧
        (s.regs 7).toNat ≠ 0 ∧ (s.regs 7).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 7).toNat 32 true = true ∧
          Fv256.B.wv s.mem (s.regs 7).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 3).toNat + 8 * L ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 3).toNat) ∧
          ((s.regs 7).toNat + 32 ≤ s.sp.toNat - 344 ∨ s.sp.toNat + 72 ≤ (s.regs 7).toNat))
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        (∀ i, i ∉ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 27] → s'.regs i = s.regs i) ∧
        Fv256.B.wv s'.mem (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 3).toNat L / Fv256.B.wv s.mem (s.regs 6).toNat 4 ∧
        Fv256.B.wv s'.mem (s.regs 7).toNat 4 = Fv256.B.wv s.mem (s.regs 3).toNat L % Fv256.B.wv s.mem (s.regs 6).toNat 4 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L), ((s.regs 7).toNat, (s.regs 7).toNat + 32),
          (s.sp.toNat - 344, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]) :=
  Fv256.Arm64.UdivremF.udivrem_rem_L hL4 hL8 Fv256.Arm64.KnuthSummary.knuth_summary

end Fv256.Arm64.UdivremFinal
