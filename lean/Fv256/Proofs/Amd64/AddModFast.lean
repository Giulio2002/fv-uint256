import Fv256.Proofs.Common.AddModProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.SpecB2
import Fv256.Proofs.Common.UtilB2
import Fv256.Proofs.Common.SpecF
import Fv256.Proofs.Common.UtilF
import Fv256.Proofs.Common.CodeIn
import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Common.ModProg
import Fv256.Proofs.Amd64.UdivremA
import Fv256.Proofs.Amd64.UdivremK
import Fv256.Proofs.Amd64.UdivremL
import Fv256.Proofs.Amd64.ModSum
import Fv256.Proofs.Amd64.AddModShapes
import Fv256.Proofs.Amd64.AddModSpecS

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModFast

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fastLL :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ AddCase s ∧ s.mem.readLE (s.regs 3).toNat 32 < s.mem.readLE (s.regs 7).toNat 32 ∧ s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32) AddPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase, hlt, hlt2⟩
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
  clear hdgz hdg hzm hzx hzy hdata
  simp only [Util.readLE_32] at hlt hlt2
  obtain ⟨hm3, hx3, hy3⟩ := hcase
  janus64_run [hz0, hx0, hy0, hm0, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (with_reducible apply Fv256.F.shape0 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape1 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape2 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape3 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape4 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape5 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape6 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape7 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape8 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape9 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape10 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape11 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption)))


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fastLG :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ AddCase s ∧ s.mem.readLE (s.regs 3).toNat 32 < s.mem.readLE (s.regs 7).toNat 32 ∧ ¬ (s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32)) AddPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase, hlt, hlt2⟩
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
  clear hdgz hdg hzm hzx hzy hdata
  simp only [Util.readLE_32] at hlt hlt2
  obtain ⟨hm3, hx3, hy3⟩ := hcase
  janus64_run [hz0, hx0, hy0, hm0, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (with_reducible apply Fv256.F.shape0 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape1 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape2 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape3 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape4 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape5 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape6 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape7 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape8 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape9 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape10 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape11 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption)))


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fastGL :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ AddCase s ∧ ¬ (s.mem.readLE (s.regs 3).toNat 32 < s.mem.readLE (s.regs 7).toNat 32) ∧ s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32) AddPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase, hlt, hlt2⟩
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
  clear hdgz hdg hzm hzx hzy hdata
  simp only [Util.readLE_32] at hlt hlt2
  obtain ⟨hm3, hx3, hy3⟩ := hcase
  janus64_run [hz0, hx0, hy0, hm0, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (with_reducible apply Fv256.F.shape0 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape1 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape2 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape3 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape4 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape5 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape6 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape7 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape8 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape9 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape10 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape11 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption)))


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem fastGG :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ AddCase s ∧ ¬ (s.mem.readLE (s.regs 3).toNat 32 < s.mem.readLE (s.regs 7).toNat 32) ∧ ¬ (s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32)) AddPost := by
  intro s hpc ⟨⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase, hlt, hlt2⟩
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
  clear hdgz hdg hzm hzx hzy hdata
  simp only [Util.readLE_32] at hlt hlt2
  obtain ⟨hm3, hx3, hy3⟩ := hcase
  janus64_run [hz0, hx0, hy0, hm0, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (with_reducible apply Fv256.F.shape0 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape1 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape2 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape3 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape4 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape5 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape6 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape7 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape8 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape9 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape10 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape11 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption)))


theorem fast :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ AddCase s) AddPost := by
  intro s hpc ⟨hpre, hc⟩
  by_cases h1 : s.mem.readLE (s.regs 3).toNat 32 < s.mem.readLE (s.regs 7).toNat 32
  · by_cases h2 : s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32
    · exact fastLL s hpc ⟨hpre, hc, h1, h2⟩
    · exact fastLG s hpc ⟨hpre, hc, h1, h2⟩
  · by_cases h2 : s.mem.readLE (s.regs 1).toNat 32 < s.mem.readLE (s.regs 7).toNat 32
    · exact fastGL s hpc ⟨hpre, hc, h1, h2⟩
    · exact fastGG s hpc ⟨hpre, hc, h1, h2⟩

end Fv256.Amd64.AddModFast
