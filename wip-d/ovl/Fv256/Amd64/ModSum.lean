import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ModSum

abbrev modEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Mod"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem mod_summary :
    Summary Extracted.program modEntry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x1e0 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x188 ∧ StackWritable s 0x1d8 0x10 ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x1d8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x1d8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 3).toNat) ∧
        ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0x1d8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 1).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x1d8 ∨ (s.regs 4).toNat + 0x10 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        s'.mem.readLE (s.regs 0).toNat 32 = Fv256.B.modSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x1d8, (s.regs 4).toNat + 0x10)]) := by
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
  have hs72 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; have := (s.regs 4).isLt; omega
  have hr1 : s.mem.accessible ((s.regs 4).toNat - 72) 32 true = true := Janus.Arm64.Memory.accessible_mono _ hacc (by omega) (by omega)
  janus64_run [hs72, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.Amd64.UdivremL.udivrem_rem]
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (have e8 : BitVec.toNat (s.regs 4) - 64 = BitVec.toNat (s.regs 4) - 72 + 8 := by omega
       have e16 : BitVec.toNat (s.regs 4) - 56 = BitVec.toNat (s.regs 4) - 72 + 16 := by omega
       have e24 : BitVec.toNat (s.regs 4) - 48 = BitVec.toNat (s.regs 4) - 72 + 24 := by omega
       rw [e8, e16, e24])
    | skip)
  all_goals (first
    | (exfalso; omega)
    | (rw [Fv256.B.modSpec]
       split <;>
         (first
           | omega
           | (exfalso; omega)
           | exact Fv256.B.zero_eq_mod_self _ _ (by omega)
           | exact (Nat.mod_eq_of_lt (by omega)).symm
           | exact Fv256.B.mod_congr _ _ _ (by omega)
           | (rw [Fv256.B.mod64_mod _ _ (by omega)]; exact Fv256.B.mod_congr _ _ _ (by omega))))
    | skip)

end Fv256.Amd64.ModSum
