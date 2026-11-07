import Fv256.AddModProg
import Fv256.Amd64.AddModSpecS
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.SegCompose

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSegA

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segA (s : State) (hpc : s.rip = BitVec.ofNat 64 addmodEntry)
    (hpre : AddPre Fv256.AddModProg.program s) (hnc : ¬ AddCase s) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (addmodEntry + 0x235)) s
      (fun S' => S'.rip = BitVec.ofNat 64 (addmodEntry + 0x235) ∧ S'.regs 4 = s.regs 4 - 360#64 ∧ S'.regs 5 = s.regs 4 - 8#64 ∧
        S'.regs 2 = BitVec.ofNat 64 (s.mem.readLE ((s.regs 7).toNat + 24) 8) ∧
        (∀ i, i ≠ 2 → i ≠ 4 → i ≠ 5 → i ≠ 12 → S'.regs i = s.regs i) ∧
        S'.xmm = s.xmm ∧ S'.df = s.df ∧ S'.mxcsr = s.mxcsr ∧
        S'.mem = s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩ := hpre
  unfold AddCase at hnc
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdgz
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hsp
  clear hdz hzm hzx hzy hdg hdgz
  janus64_data hdata [hacc]
  have hnc' : s.mem.readLE ((s.regs 7).toNat + 24) 8 = 0 ∨ s.mem.readLE ((s.regs 7).toNat + 24) 8 < s.mem.readLE ((s.regs 3).toNat + 24) 8 ∨
      s.mem.readLE ((s.regs 7).toNat + 24) 8 < s.mem.readLE ((s.regs 1).toNat + 24) 8 := by
    by_cases h1 : s.mem.readLE ((s.regs 7).toNat + 24) 8 = 0
    · exact Or.inl h1
    · by_cases h2 : s.mem.readLE ((s.regs 7).toNat + 24) 8 < s.mem.readLE ((s.regs 3).toNat + 24) 8
      · exact Or.inr (Or.inl h2)
      · by_cases h3 : s.mem.readLE ((s.regs 7).toNat + 24) 8 < s.mem.readLE ((s.regs 1).toNat + 24) 8
        · exact Or.inr (Or.inr h3)
        · exfalso; apply hnc; exact ⟨h1, by omega, by omega⟩
  rcases hnc' with h | h | h
  all_goals (janus64_run until [addmodEntry + 0x235])
  all_goals (intro i h2 h4 h5 h12; simp [h2, h4, h5, h12])

end Fv256.Amd64.AddModSegA
