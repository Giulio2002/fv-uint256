import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Amd64.UdivremA
import Fv256.Proofs.Amd64.UdivremK
import Fv256.Proofs.Amd64.UdivremL
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.DivProg
import Fv256.Proofs.Common.SDivProg
import Fv256.Proofs.Amd64.DivSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SDivSum

set_option maxRecDepth 100000 in
theorem hcLib : Janus.Contracts.EqHashModel.CodeIn64 Fv256.DivProg.program Fv256.SDivProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

namespace Local
open Fv256.B

theorem abs_zero : Fv256.Spec.abs 0 = 0 := by simp [Fv256.Spec.abs]
theorem neg_zero : Fv256.Spec.neg 0 = 0 := by simp [Fv256.Spec.neg, Fv256.Spec.W]

theorem sdivSpec_x0 (x y : Nat) (h : x = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_left]

theorem sdivSpec_y0 (x y : Nat) (h : y = 0) : sdivSpec x y = 0 := by
  subst h; unfold sdivSpec; simp [abs_zero, neg_zero, divSpec_zero_right]

theorem sdivSpec_zl (y : Nat) : sdivSpec 0 y = 0 := sdivSpec_x0 0 y rfl
theorem sdivSpec_zr (x : Nat) : sdivSpec x 0 = 0 := sdivSpec_y0 x 0 rfl

end Local

abbrev sdivEntry : Nat := segAddr Fv256.SDivProg.program "github.com/holiman/uint256.(*Int).SDiv"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem sdiv_summary :
    Summary Fv256.SDivProg.program sdivEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x268 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x210 ∧ StackWritable s 0x260 0x10 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x260 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x260 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0x260 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x260 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.sdivSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x260, (s.regs 4).toNat + 0x10)]) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, hdz, hdx, hdy, hdg⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2
  simp only [regSP] at hacc hlow hnw
  have hx0 := Util.readLE8_lt s.mem (s.regs 3).toNat
  have hx1 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 8)
  have hx2 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 16)
  have hx3 := Util.readLE8_lt s.mem ((s.regs 3).toNat + 24)
  have hy0 := Util.readLE8_lt s.mem (s.regs 1).toNat
  have hy1 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 8)
  have hy2 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 16)
  have hy3 := Util.readLE8_lt s.mem ((s.regs 1).toNat + 24)
  have hdv := Nat.div_le_self (s.mem.readLE (s.regs 3).toNat 8) (s.mem.readLE (s.regs 1).toNat 8)
  janus64_run [Util.msb_m1, Util.msb_0, Util.msb_1, Util.readLE_32, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff] calls [Fv256.CodeIn.lib_summary hcLib Fv256.Amd64.DivSum.div_summary]
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (simp only [Local.sdivSpec_zl, Local.sdivSpec_zr])
    | skip)
  all_goals (
    have nx := Util.neg_chain _ _ _ _ hx0 hx1 hx2 hx3
    have ny := Util.neg_chain _ _ _ _ hy0 hy1 hy2 hy3
    have nz := Util.neg_chain _ _ _ _ (Util.readLE8_lt s'.mem (s.regs 0).toNat) (Util.readLE8_lt s'.mem ((s.regs 0).toNat + 8))
      (Util.readLE8_lt s'.mem ((s.regs 0).toNat + 16)) (Util.readLE8_lt s'.mem ((s.regs 0).toNat + 24))
    simp only [nx, ny, nz, Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right] at *
    rw [Fv256.B.sdivSpec]
    simp only [Fv256.Spec.abs, Fv256.Spec.neg, Fv256.Spec.W, Nat.reducePow]
    simp (disch := omega) only [if_pos, if_neg, Fv256.B.divSpec_zero_left, Fv256.B.divSpec_zero_right]
    omega)

end Fv256.Amd64.SDivSum
