import Fv256.Proofs.Arm64.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Arm64.UdivremFront
import Fv256.Proofs.Arm64.UdivremA
import Fv256.Proofs.Arm64.UdivremD
import Fv256.Proofs.Arm64.UdivremE

/-!
# arm64 `udivrem`: the `rem = nil` and `rem != nil` entries (mirror of `Fv256.Amd64.UdivremL`)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.UdivremA Fv256.Arm64.UdivremFront Fv256.Arm64.UdivremD Fv256.Arm64.UdivremE

namespace Fv256.Arm64.UdivremF

theorem rr_mono' {p : Program} {ret : W64} {s : State} {Q Q' : State → Prop} (h : ReachesRet p ret s Q)
    (hQ : ∀ S, Q S → Q' S) : ReachesRet p ret s Q' := by
  obtain ⟨k, s', hs, hp, hq⟩ := h
  exact ⟨k, s', hs, hp, hQ _ hq⟩

/-- `udivrem(quot, u, d, nil)`: only the quotient is produced (`L` limbs, `4 <= L <= 8`). -/
theorem udivrem_nil_L {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) (hKn : KnuthStmt) :
    Summary Fv256.Arm64.ChainProg.program ku
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
          (s.sp.toNat + 8, s.sp.toNat + 72)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hr⟩
  have h := udivrem_summary_L hL4 hL8 hKn s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, fun h => absurd hr h⟩
  refine rr_mono' h ?_
  rintro S ⟨a1, a2, a3, a4, a5, a6, a7, ⟨b1, b2, b3, b4⟩⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, b1, b3 hr⟩

/-- `udivrem(quot, u, d, rem)` with a non-nil `rem`. -/
theorem udivrem_rem_L {L : Nat} (hL4 : 4 ≤ L) (hL8 : L ≤ 8) (hKn : KnuthStmt) :
    Summary Fv256.Arm64.ChainProg.program ku
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
          (s.sp.toNat - 344, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 72)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hr, hb, ha, hz, d1, d2, d3⟩
  have h := udivrem_summary_L hL4 hL8 hKn s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, fun _ => ⟨hb, ha, hz, d1, d2, d3⟩⟩
  refine rr_mono' h ?_
  rintro S ⟨a1, a2, a3, a4, a5, a6, a7, ⟨b1, b2, b3, b4⟩⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, b1, b2 hr, b4 hr⟩

end Fv256.Arm64.UdivremF
