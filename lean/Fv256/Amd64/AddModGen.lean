import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.ChainProg
import Fv256.ModProg
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL
import Fv256.Amd64.ModSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.AddModGen

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gen (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => (fun s => StackGuardOK s 0x300 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x348 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16) ∧
        ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16)) s ∧ ¬ (s.mem.readLE (m.toNat + 24) 8 ≠ 0 ∧ s.mem.readLE (x.toNat + 24) 8 ≤ s.mem.readLE (m.toNat + 24) 8 ∧ s.mem.readLE (y.toNat + 24) 8 ≤ s.mem.readLE (m.toNat + 24) 8))
      (fun s s' => s'.regs 0 = z ∧ s'.mem.readLE z.toNat 32 = Fv256.F.addmodSpec (s.mem.readLE x.toNat 32) (s.mem.readLE y.toNat 32) (s.mem.readLE m.toNat 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x348, (s.regs regSP).toNat + 0x28)]) := by
  intro ret hret s hs ⟨⟨hg, hsp, ⟨hlow, hnw, hacc⟩, hdata, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdgz
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hsp
  janus64_data hdata [hacc]
  have bm3 := Util.readLE8_lt s.mem (m.toNat + 24)
  have bx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have by3 := Util.readLE8_lt s.mem (y.toNat + 24)
  rcases hzm with rfl | hzm <;> rcases hzx with rfl | hzx <;> rcases hzy with rfl | hzy
  all_goals (janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 5) (by omega)), Fv256.CodeIn.lib_summary hcMod Fv256.Amd64.ModSum.mod_summary])
  all_goals (first | (exfalso; omega) | skip)
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first | (simp only [Fv256.F.addmodSpec]; simp; done) | skip)
  all_goals (first
    | (refine Fv256.F.close_mod _ _ _ _ _ ?_ ?_ (by with_reducible assumption)
       · exact Fv256.F.add4_val _ _ _ _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
       · exact (Fv256.F.add4_flag _ _ _ _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)).symm.trans (Fv256.F.noov_of _ (by with_reducible assumption)))
    | (have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
         janus64_data hdata [hz]
         first | exact h_ddisj0_0 | assumption
       have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by
         rw [h_rodata _ _ (by decide)]; decide
       have key := (show Janus.Arm64.Memory.readLE _ (BitVec.toNat (s.regs 4) - 160) 8 + 18446744073709551616 * Janus.Arm64.Memory.readLE _ (BitVec.toNat (s.regs 4) - 160 + 8) 8 + _ = _ by with_reducible assumption)
       simp (disch := omega) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
         Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
       have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega
       have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega
       have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega
       have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega
       have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega
       have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega
       have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega
       have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega
       simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
       have hv := Fv256.F.add4_val _ _ _ _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
       have hf := Fv256.F.add4_flag _ _ _ _ _ _ _ _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
       have ho := Fv256.F.ov_of _ (by with_reducible assumption)
       rw [key]
       unfold Fv256.F.addmodSpec
       rw [if_neg (by intro h; omega)]
       refine congrArg (fun t => t % _) ?_
       omega))

end Fv256.Amd64.AddModGen
