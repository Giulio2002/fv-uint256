import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.CodeIn
import Fv256.DivProg
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.DivSum

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.DivProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

abbrev divEntry : Nat := segAddr Fv256.DivProg.program "github.com/holiman/uint256.(*Int).Div"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem div_summary :
    Summary Fv256.DivProg.program divEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x1c0 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x168 ∧ StackWritable s 0x1b8 0x10 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x1b8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x1b8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0x1b8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x1b8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.divSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x1b8, (s.regs 4).toNat + 0x10)]) := by
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
  janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcChain Fv256.Amd64.UdivremL.udivrem_nil]
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (have e8 : BitVec.toNat (s.regs 4) - 32 = BitVec.toNat (s.regs 4) - 40 + 8 := by omega
       have e16 : BitVec.toNat (s.regs 4) - 24 = BitVec.toNat (s.regs 4) - 40 + 16 := by omega
       have e24 : BitVec.toNat (s.regs 4) - 16 = BitVec.toNat (s.regs 4) - 40 + 24 := by omega
       rw [e8, e16, e24])
    | skip)
  all_goals (first
    | (exfalso; omega)
    | (rw [Fv256.B.divSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | exact Fv256.B.one_eq_div _ _ (by omega) (by omega)
           | exact (Nat.div_eq_of_lt (by omega)).symm
           | exact Fv256.B.div_congr _ _ _ (by omega)))
    | skip)

end Fv256.Amd64.DivSum
