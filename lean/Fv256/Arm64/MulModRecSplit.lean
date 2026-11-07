import Fv256.Arm64.MulModRecProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF
import Fv256.Arm64.ReduceSpec
import Fv256.Arm64.MulModRecSum

/-!
# arm64 `MulModWithReciprocal` library summary split by the number of limbs of `m` (for wrappers that case-split)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.MulModRecSum

namespace Fv256.Arm64.MulModRecSplit

def preNoMu (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 720 ∧ StackOK s 760 48 ∧
  Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 760) 808 ∧
  ((s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧ Apart (s.regs 0).toNat 32 (s.sp.toNat - 760) 808) ∧
  ((s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧ Apart (s.regs 1).toNat 32 (s.sp.toNat - 760) 808) ∧
  ((s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧ Apart (s.regs 2).toNat 32 (s.sp.toNat - 760) 808) ∧
  ((s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧ Apart (s.regs 3).toNat 32 (s.sp.toNat - 760) 808) ∧
  ((s.regs 4).toNat + 40 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 4).toNat 40 false = true ∧ Apart (s.regs 4).toNat 40 (s.sp.toNat - 760) 808)

theorem mulmodrec_small (hR4 : Fv256.Arm64.ReduceSpec.R4Summary) :
    Summary Fv256.Arm64.MulModRecProg.program mulmodrecEntry
    (fun s => preNoMu s ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 = 0)
    (fun s s' => s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 760, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 48)]) :=
  fun s hpc ⟨hp, hd⟩ => Fv256.Arm64.MulModRecSum.mulmodrec_summary hR4 s hpc (by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hp
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, ?_⟩
    unfold Fv256.F.MuOK
    intro h
    exfalso
    rw [Util.readLE_32] at h
    have x0 := Util.readLE8_lt s.mem (s.regs 3).toNat
    have x1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
    have x2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
    simp only [hd, Nat.mul_zero, Nat.add_zero] at h
    omega)

theorem mulmodrec_big (hR4 : Fv256.Arm64.ReduceSpec.R4Summary) :
    Summary Fv256.Arm64.MulModRecProg.program mulmodrecEntry
    (fun s => preNoMu s ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 ≠ 0 ∧
      Fv256.F.RecipWeak (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 4).toNat 40))
    (fun s s' => s'.sp = s.sp ∧ s'.regs 0 = s.regs 0 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 28 = s.regs 28 ∧
        s'.regs 29 = s.regs 29 ∧ s'.regs 30 = s.regs 30 ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 1).toNat 32)
          (s.mem.readLE (s.regs 2).toNat 32) (s.mem.readLE (s.regs 3).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat - 760, s.sp.toNat - 8),
          (s.sp.toNat + 8, s.sp.toNat + 48)]) :=
  fun s hpc ⟨hp, hd, hw⟩ => Fv256.Arm64.MulModRecSum.mulmodrec_summary hR4 s hpc (by
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hp
    exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fun _ => hw⟩)


end Fv256.Arm64.MulModRecSplit
