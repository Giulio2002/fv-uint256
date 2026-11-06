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
import Fv256.UtilAM
import Fv256.Amd64.AddModTac
import Fv256.Amd64.AddModShapes
import Janus.Tactic.CarryNf

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSegCov

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option hygiene false in
macro "segCov_closeq" "[" es:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine ⟨fun i h11 h12 => by simp [setRegF, h11, h12], ?_, ?_⟩
  · (try clear hbr); (try clear hov); (try clear hzx hzy); (try clear hzx'); (try clear hzy')
    janus_frame
  · (try dsimp only)
    (try simp (disch := (keep_only hzb hzx' hzy'; omega)) only [Util.readLE_32, Janus.Arm64.Memory.readLE_writeLE_self, Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
    (try simp only [Fv256.F.ite_dec, Bool.toNat_false, BitVec.toNat_ofNat, Nat.reducePow, Util.readLE8_mod, $es,*] at *)
    (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.F.dec_div] at *)
    clear_env_facts
    janus_carry_nf at *
    janus_omega_values))

set_option hygiene false in
macro "segCov_closeh" "[" es:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  exfalso
  (try simp only [$es,*] at hov)
  (try simp only [Fv256.F.ite_dec, Bool.toNat_false, BitVec.toNat_ofNat, Nat.reducePow, Util.readLE8_mod, $es,*] at *)
  (try simp (disch := (keep_only bx0 bx1 bx2 bx3 by0 by1 by2 by3; decide_facts; omega)) only [Fv256.F.dec_div] at *)
  clear_env_facts
  janus_carry_nf at *
  janus_omega_values))

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segCov (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x296))
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hxb : (S.regs 3).toNat + 32 ≤ 2 ^ 48) (hxa : S.mem.accessible (S.regs 3).toNat 32 false = true)
    (hyb : (S.regs 1).toNat + 32 ≤ 2 ^ 48) (hya : S.mem.accessible (S.regs 1).toNat 32 false = true)
    (hzx : S.regs 0 = S.regs 3 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 3).toNat ∨ (S.regs 3).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hov : 2 ^ 256 ≤ S.mem.readLE (S.regs 3).toNat 32 + S.mem.readLE (S.regs 1).toNat 32) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (addmodEntry + 0x2de)) S (fun S' => S'.rip = BitVec.ofNat 64 (addmodEntry + 0x2de) ∧ (∀ i, i ≠ 11 → i ≠ 12 → S'.regs i = S.regs i) ∧
        S'.xmm = S.xmm ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32)] ∧
        S'.mem.readLE (S.regs 0).toNat 32 + 2 ^ 256 = S.mem.readLE (S.regs 3).toNat 32 + S.mem.readLE (S.regs 1).toNat 32) := by
  have bx0 := Util.readLE8_lt S.mem (S.regs 3).toNat
  have bx1 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 8)
  have bx2 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 16)
  have bx3 := Util.readLE8_lt S.mem ((S.regs 3).toNat + 24)
  have by0 := Util.readLE8_lt S.mem (S.regs 1).toNat
  have by1 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 8)
  have by2 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 16)
  have by3 := Util.readLE8_lt S.mem ((S.regs 1).toNat + 24)
  by_cases e1 : S.regs 0 = S.regs 3 <;> by_cases e2 : S.regs 0 = S.regs 1
  · have e1n : (S.regs 3).toNat = (S.regs 0).toNat := by rw [← e1]
    have e2n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e2]
    have hzx' := hzb
    have hzy' := hzb
    janus64_run [Util.readLE_32, e1n, e2n] until [addmodEntry + 0x3e5, addmodEntry + 0x2de]
    case hq => segCov_closeq [e1n, e2n]
    case h => segCov_closeh [e1n, e2n]
  · have hzy' := hzy.resolve_left e2
    have e1n : (S.regs 3).toNat = (S.regs 0).toNat := by rw [← e1]
    have hzx' := hzb
    janus64_run [Util.readLE_32, e1n] until [addmodEntry + 0x3e5, addmodEntry + 0x2de]
    case hq => segCov_closeq [e1n]
    case h => segCov_closeh [e1n]
  · have hzx' := hzx.resolve_left e1
    have e2n : (S.regs 1).toNat = (S.regs 0).toNat := by rw [← e2]
    have hzy' := hzb
    janus64_run [Util.readLE_32, e2n] until [addmodEntry + 0x3e5, addmodEntry + 0x2de]
    case hq => segCov_closeq [e2n]
    case h => segCov_closeh [e2n]
  · have hzx' := hzx.resolve_left e1
    have hzy' := hzy.resolve_left e2
    janus64_run [Util.readLE_32] until [addmodEntry + 0x3e5, addmodEntry + 0x2de]
    case hq => segCov_closeq [Nat.add_zero]
    case h => segCov_closeh [Nat.add_zero]

end Fv256.Amd64.AddModSegCov
