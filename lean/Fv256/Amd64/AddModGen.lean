import Fv256.AddModProg
import Fv256.Amd64.AddModSpecS
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
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModGen

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
set_option profiler true in
set_option profiler.threshold 20000 in
theorem gen :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ ¬ AddCase s) AddPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase⟩
  unfold AddPost
  unfold AddCase at hcase
  generalize hz0 : s.regs 0 = z at *
  generalize hx0 : s.regs 3 = x at *
  generalize hy0 : s.regs 1 = y at *
  generalize hm0 : s.regs 7 = m at *
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
  all_goals (janus64_run [hz0, hx0, hy0, hm0, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 5) (by omega)), Fv256.CodeIn.lib_summary hcMod Fv256.Amd64.ModSum.mod_summary])
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
