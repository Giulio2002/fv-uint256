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
import Fv256.ChainProg
import Fv256.ModProg
import Fv256.Amd64.UdivremL
import Fv256.Amd64.ModSum

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS

namespace Fv256.Amd64.AddModSegE

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Fv256.AddModProg.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

-- `0x2de` (after the overflowing add; `z` holds the low 256 bits): `udivrem(5 limbs)` then the epilogue and `ret`.
set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segE (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x2de))
    (hx15 : S.xmm 15 = 0) (hret : S.mem.readLE ((S.regs 4).toNat + 0x168) 8 < 2 ^ 47)
    (hdacc : S.mem.accessible 5184320 96 false = true) (hrod : S.mem.readLE 5184344 16 = 18446744073709551616)
    (hdd1 : (S.regs 4).toNat - 0x158 + 0x2e8 ≤ 5184320 ∨ 5184320 + 96 ≤ (S.regs 4).toNat - 0x158)
    (hdd2 : (S.regs 0).toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ (S.regs 0).toNat)
    (hlow : 0x158 ≤ (S.regs 4).toNat) (hnw : (S.regs 4).toNat + 0x190 ≤ 2 ^ 48)
    (hacc : S.mem.accessible ((S.regs 4).toNat - 0x158) 0x2e8 true = true)
    (hgl : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true)
    (hgn : (S.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hgb : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 0x100 < (S.regs 4).toNat)
    (hz : Buffer S (S.regs 0) 32 true) (hm : Buffer S (S.regs 2) 32 false)
    (hmne : ¬ (S.mem.readLE (S.regs 2).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 24) 8 = 0))
    (hdz : (S.regs 0).toNat + 32 ≤ (S.regs 4).toNat - 0x158 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 0).toNat)
    (hdm : (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat - 0x158 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 2).toNat ∨
      ((S.regs 4).toNat + 0x140 ≤ (S.regs 2).toNat ∧ (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat + 0x170))
    (hdg : ((S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 0x158 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 14).toNat + 16)) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 0x168) 8)) S
      (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 0x170#64 ∧
        S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
        S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        S'.mem.readLE (S.regs 0).toNat 32 = (S.mem.readLE (S.regs 0).toNat 32 + 2 ^ 256) % S.mem.readLE (S.regs 2).toNat 32 ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), ((S.regs 4).toNat - 0x158, (S.regs 4).toNat + 0x190)]) := by
  obtain ⟨hzw, hza⟩ := hz
  obtain ⟨hmw, hma⟩ := hm
  have hmne' : ¬ (S.mem.readLE (S.regs 2).toNat 8 + 18446744073709551616 * S.mem.readLE ((S.regs 2).toNat + 8) 8 + 340282366920938463463374607431768211456 * S.mem.readLE ((S.regs 2).toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * S.mem.readLE ((S.regs 2).toNat + 24) 8 = 0) := by
    intro h; apply hmne; omega
  janus64_run [hrod, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 5) (by omega))]
  refine ⟨?val, ?fr⟩
  case fr => janus_frame
  rename_i hL1 hL2 hR
  have key := hL2
  clear hL1 hL2 hR
  simp (disch := omega) only [Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint,
      Janus.Arm64.Memory.readLE_writeLE_inside] at key
  have a1 : (S.regs 4).toNat + 128 - ((S.regs 4).toNat + 128) = 0 := by omega
  have a2 : (S.regs 4).toNat + 128 + 8 - ((S.regs 4).toNat + 128) = 8 := by omega
  have a3 : (S.regs 4).toNat + 128 + 8 + 8 - ((S.regs 4).toNat + 144) = 0 := by omega
  have a4 : (S.regs 4).toNat + 128 + 8 + 8 + 8 - ((S.regs 4).toNat + 152) = 0 := by omega
  have a5 : (S.regs 4).toNat + 128 + 8 + 8 + 8 + 8 - ((S.regs 4).toNat + 152) = 8 := by omega
  have b1 : (S.regs 4).toNat + 200 + 8 = (S.regs 4).toNat + 208 := by omega
  have b2 : (S.regs 4).toNat + 200 + 16 = (S.regs 4).toNat + 216 := by omega
  have b3 : (S.regs 4).toNat + 200 + 24 = (S.regs 4).toNat + 224 := by omega
  simp only [a1, a2, a3, a4, a5, b1, b2, b3, Nat.reducePow, Nat.div_one] at key
  have bnd0 := Util.readLE8_lt S.mem (S.regs 0).toNat
  have bnd1 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 8)
  have bnd2 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 16)
  have bnd3 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 24)
  rw [key]
  refine congrArg (fun t => t % _) ?_
  omega

end Fv256.Amd64.AddModSegE
