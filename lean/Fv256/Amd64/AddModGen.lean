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
import Fv256.Amd64.AddModShapes
import Fv256.Amd64.AddModShapesG
import Fv256.Amd64.AddModTac
import Fv256.Amd64.AddModTac

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
  · -- goal 0: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 1
    with_reducible apply Fv256.F.gA1 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 2
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s)
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 3: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 4
    with_reducible apply Fv256.F.gA4 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 5
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 6
    with_reducible apply Fv256.F.gA6 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 7
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 8: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 9
    with_reducible apply Fv256.F.gA9 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 10
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s)
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) 0 (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (by omega_s)
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 11
    with_reducible apply Fv256.F.gA11 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 12
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 13: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 14
    with_reducible apply Fv256.F.gA14 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 15
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 16
    with_reducible apply Fv256.F.gA16 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 17
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 18
    with_reducible apply Fv256.F.gA18 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 19
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 20: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 21
    with_reducible apply Fv256.F.gA21 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 22
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 23
    with_reducible apply Fv256.F.gA23 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 24
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 25: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 26
    with_reducible apply Fv256.F.gA26 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 27
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 28
    with_reducible apply Fv256.F.gA28 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 29
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 30
    with_reducible apply Fv256.F.gA30 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 31
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 32: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 33
    with_reducible apply Fv256.F.gA33 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 34
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 35
    with_reducible apply Fv256.F.gA35 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 36
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 37
    with_reducible apply Fv256.F.gA37 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 38
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (z.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (z.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (z.toNat)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (z.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 39: m = 0
    simp [Fv256.F.addmodSpec]
  · -- goal 40
    with_reducible apply Fv256.F.gA40 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 41
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 42
    with_reducible apply Fv256.F.gA42 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 43
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    
  · -- goal 44
    with_reducible apply Fv256.F.gA44 <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)
  · -- goal 45
    rename_i hL1 hL2 hR
    have key := hL2
    clear hL1 hL2 hR
    have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
    have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
      janus64_data hdata [hz]
      first | exact h_ddisj0_0 | assumption
    simp (disch := (clear key; omega_s)) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_inside, hrodv] at key
    have a1 : BitVec.toNat (s.regs 4) - 232 - (BitVec.toNat (s.regs 4) - 232) = 0 := by omega_s
    have a2 : BitVec.toNat (s.regs 4) - 232 + 8 - (BitVec.toNat (s.regs 4) - 232) = 8 := by omega_s
    have a3 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 - (BitVec.toNat (s.regs 4) - 216) = 0 := by omega_s
    have a4 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 0 := by omega_s
    have a5 : BitVec.toNat (s.regs 4) - 232 + 8 + 8 + 8 + 8 - (BitVec.toNat (s.regs 4) - 208) = 8 := by omega_s
    have b1 : BitVec.toNat (s.regs 4) - 160 + 8 = BitVec.toNat (s.regs 4) - 152 := by omega_s
    have b2 : BitVec.toNat (s.regs 4) - 160 + 16 = BitVec.toNat (s.regs 4) - 144 := by omega_s
    have b3 : BitVec.toNat (s.regs 4) - 160 + 24 = BitVec.toNat (s.regs 4) - 136 := by omega_s
    simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
    have bnd0 := (Fv256.Util.readLE8_lt s.mem (x.toNat))
    have bnd1 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
    have bnd2 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
    have bnd3 := (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
    have bnd4 := (Fv256.Util.readLE8_lt s.mem (y.toNat))
    have bnd5 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 8))
    have bnd6 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 16))
    have bnd7 := (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hv := Fv256.F.add4_val (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    have hf := Fv256.F.add4_flag (Janus.Arm64.Memory.readLE s.mem (x.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (x.toNat + 24) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 8) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 16) 8) (Janus.Arm64.Memory.readLE s.mem (y.toNat + 24) 8) (Fv256.Util.readLE8_lt s.mem (x.toNat)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (x.toNat + 24)) (Fv256.Util.readLE8_lt s.mem (y.toNat)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 8)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 16)) (Fv256.Util.readLE8_lt s.mem (y.toNat + 24))
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.reducePow] at hv hf
    have ho := Fv256.F.ov_of _ hbr
    rw [key]
    unfold Fv256.F.addmodSpec
    rw [if_neg (by omega_s)]
    refine congrArg (fun t => t % _) ?_
    all_goals (decide_facts; omega_s)
    

end Fv256.Amd64.AddModGen
