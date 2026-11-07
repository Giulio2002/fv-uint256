import Fv256.Arm64.AddModProg
import Fv256.Arm64.AddModEntry
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.UtilMDO
import Fv256.Arm64.SummaryEnsures
import Fv256.Arm64.ModSum
import Fv256.Arm64.UdivremFinal
import Fv256.Arm64.ChainProg
import Fv256.Arm64.ModProg
import Fv256.Arm64.CodeIn
import Fv256.UtilAM
import Fv256.Amd64.AddModTac
import Fv256.Arm64.AddModSegB
import Janus.Tactic.CarryNf

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec
open Fv256.Arm64.AddModSegB (ne_limbs)

namespace Fv256.Arm64.AddModSegE

set_option maxRecDepth 200000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ChainProg.program Fv256.Arm64.AddModProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 200000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn Fv256.Arm64.ModProg.program Fv256.Arm64.AddModProg.program :=
  Fv256.Arm64.CodeIn.codeIn_of_sub _ _ (by decide) (by decide) (by decide)

abbrev PreS (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ GuardOK s 816 ∧
    s.sp.toNat % 16 = 0 ∧ 856 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 48 ∧ s.mem.accessible (s.sp.toNat - 856) 872 true = true ∧
    Fv256.Arm64.AddModProg.program.DataLoaded s.mem ∧
    ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 28).toNat + 16) ∧
    (s.regs 0).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 0).toNat 32 true = true ∧
    (s.regs 1).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 1).toNat 32 false = true ∧
    (s.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 2).toNat 32 false = true ∧
    (s.regs 3).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 3).toNat 32 false = true ∧
    ((s.regs 0).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 0).toNat) ∧
    ((s.regs 1).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 1).toNat) ∧
    ((s.regs 2).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 2).toNat) ∧
    ((s.regs 3).toNat + 32 ≤ s.sp.toNat - 856 ∨ s.sp.toNat + 16 ≤ (s.regs 3).toNat) ∧
    (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 1 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat) ∧
    (s.regs 0 = s.regs 2 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 2).toNat ∨ (s.regs 2).toNat + 32 ≤ (s.regs 0).toNat) ∧
    ((s.regs 28).toNat + 24 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 28).toNat + 16)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segE (S : State) (hpc : S.pc = BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x25c))
    (hsal : S.sp.toNat % 16 = 0) (hsb : 344 ≤ S.sp.toNat) (hsc : S.sp.toNat + 384 ≤ 2 ^ 48)
    (hsw : S.mem.accessible (S.sp.toNat - 344) 728 true = true)
    (hrod : S.mem.accessible 1010368 32 false = true)
    (hzb : (S.regs 0).toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible (S.regs 0).toNat 32 true = true)
    (hdz : (S.regs 0).toNat + 32 ≤ S.sp.toNat - 344 ∨ S.sp.toNat + 384 ≤ (S.regs 0).toNat) :
    Janus.Tactic.ReachesRet Fv256.Arm64.AddModProg.program (BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x2f4)) S
      (fun S' => S'.pc = BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x2f4) ∧ S'.sp = S.sp ∧
        S'.regs 0 = S.sp + 248#64 ∧ S'.regs 1 = 5#64 ∧ S'.regs 2 = 5#64 ∧ S'.regs 3 = S.sp + 144#64 ∧ S'.regs 4 = 5#64 ∧
        S'.regs 5 = 5#64 ∧ S'.regs 6 = S.regs 8 ∧ S'.regs 7 = S.sp + 216#64 ∧
        (∀ i, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 9 → i ≠ 10 → i ≠ 11 → i ≠ 12 → i ≠ 13 → i ≠ 27 →
          S'.regs i = S.regs i) ∧
        MemFrame S.mem S'.mem [(S.sp.toNat + 144, S.sp.toNat + 328), (S.sp.toNat + 376, S.sp.toNat + 384)] ∧
        S'.mem.readLE (S.sp.toNat + 376) 8 = (S.regs 0).toNat ∧
        Fv256.B.wv S'.mem (S.sp.toNat + 144) 5 = S.mem.readLE (S.regs 0).toNat 32 + 2 ^ 256 ∧
        Fv256.B.wv S'.mem (S.sp.toNat + 216) 4 = 0 ∧ Fv256.B.wv S'.mem (S.sp.toNat + 248) 5 = 0) := by
  janus_run [Util.readLE_32] until [Fv256.Arm64.AddModProg.entry + 0x2f4]
  apply Janus.Tactic.ReachesRet.done
  · simp [Fv256.Arm64.AddModProg.entry]
  refine ⟨by simp [Fv256.Arm64.AddModProg.entry], rfl, by simp [setReg], by simp [setReg], by simp [setReg], by simp [setReg], by simp [setReg],
    by simp [setReg], by simp [setReg], by simp [setReg], fun i h0 h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 h27 => by
      simp [setReg, h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13, h27], ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    janus_frame
  · dsimp only
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (S.regs 0).isLt; simpa using this)
  · dsimp only
    have b0 := Util.readLE8_lt S.mem (S.regs 0).toNat
    have b1 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 8)
    have b2 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 16)
    have b3 := Util.readLE8_lt S.mem ((S.regs 0).toNat + 24)
    simp (disch := omega) only [Fv256.B.wv_writeLE_outside, Fv256.B.wv_succ, Fv256.B.wv, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    simp only [Nat.reducePow, Util.readLE8_mod, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero, Nat.one_mod]
    rw [Util.readLE_32]
    omega
  · dsimp only
    simp (disch := omega) only [Fv256.F.wv_zero4w]
  · dsimp only
    simp (disch := omega) only [Fv256.B.wv_writeLE_outside, Fv256.F.wv_zero5w]


set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem segF (S : State) (R X29 zv : BitVec 64) (V : Nat) (hpc : S.pc = BitVec.ofNat 64 (Fv256.Arm64.AddModProg.entry + 0x2f4))
    (hsal : S.sp.toNat % 16 = 0) (hsb : 344 ≤ S.sp.toNat) (hsc : S.sp.toNat + 384 ≤ 2 ^ 48)
    (hsw : S.mem.accessible (S.sp.toNat - 344) 728 true = true)
    (hr0 : S.regs 0 = S.sp + 248#64) (hr1 : S.regs 1 = 5#64) (hr2 : S.regs 2 = 5#64) (hr3 : S.regs 3 = S.sp + 144#64)
    (hr4 : S.regs 4 = 5#64) (hr5 : S.regs 5 = 5#64) (hr7 : S.regs 7 = S.sp + 216#64)
    (hq0 : Fv256.B.wv S.mem (S.sp.toNat + 248) 5 = 0) (hrem0 : Fv256.B.wv S.mem (S.sp.toNat + 216) 4 = 0)
    (hsum : Fv256.B.wv S.mem (S.sp.toNat + 144) 5 = V + 2 ^ 256) (hspill : S.mem.readLE (S.sp.toNat + 376) 8 = zv.toNat)
    (hg1 : (S.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible ((S.regs 28).toNat + 16) 8 false = true)
    (hg3 : S.mem.readLE ((S.regs 28).toNat + 16) 8 + 304 < S.sp.toNat)
    (hgw : (S.regs 28).toNat + 24 ≤ S.sp.toNat - 344 ∨ S.sp.toNat + 384 ≤ (S.regs 28).toNat + 16)
    (hzb : zv.toNat + 32 ≤ 2 ^ 48) (hza : S.mem.accessible zv.toNat 32 true = true)
    (hmb : (S.regs 6).toNat + 32 ≤ 2 ^ 48) (hma : S.mem.accessible (S.regs 6).toNat 32 false = true)
    (hdz : zv.toNat + 32 ≤ S.sp.toNat - 344 ∨ S.sp.toNat + 384 ≤ zv.toNat)
    (hdm : (S.regs 6).toNat + 32 ≤ S.sp.toNat - 344 ∨ (S.regs 6).toNat = S.sp.toNat + 328 ∨ S.sp.toNat + 384 ≤ (S.regs 6).toNat)
    (hm32 : S.mem.readLE (S.regs 6).toNat 32 ≠ 0)
    (hret : S.mem.readLE S.sp.toNat 8 = R.toNat) (hRa : R.toNat % 4 = 0) (hRb : R.toNat < 2 ^ 56)
    (hx29 : S.mem.readLE (S.sp.toNat - 8) 8 = X29.toNat) :
    Janus.Tactic.ReachesRet Fv256.Arm64.AddModProg.program R S
      (fun S' => S'.pc = R ∧ S'.sp = S.sp + 368 ∧ S'.regs 0 = zv ∧ S'.regs 28 = S.regs 28 ∧ S'.regs 29 = X29 ∧ S'.regs 18 = S.regs 18 ∧
        S'.regs 30 = R ∧
        S'.mem.readLE zv.toNat 32 = (V + 2 ^ 256) % S.mem.readLE (S.regs 6).toNat 32 ∧
        MemFrame S.mem S'.mem [(zv.toNat, zv.toNat + 32), (S.sp.toNat - 344, S.sp.toNat + 360), (S.sp.toNat + 376, S.sp.toNat + 384)]) := by
  have e216 : (S.sp + 216#64).toNat = S.sp.toNat + 216 := by simp [BitVec.toNat_add]; omega
  have e248 : (S.sp + 248#64).toNat = S.sp.toNat + 248 := by simp [BitVec.toNat_add]; omega
  have e144 : (S.sp + 144#64).toNat = S.sp.toNat + 144 := by simp [BitVec.toNat_add]; omega
  have hmw : Fv256.B.wv S.mem (S.regs 6).toNat 4 ≠ 0 := by rw [Fv256.B.wv4_eq]; exact hm32
  janus_run [hr0, hr1, hr2, hr3, hr4, hr5, hr7, e216, e248, e144, hret, hx29, hspill, hmw, hq0, hrem0, hsum, Util.readLE_32, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] until [Fv256.Arm64.AddModProg.entry + 0x2f8] calls [Janus.Contracts.EqHashModel.Summary.of_codeIn hcChain (Fv256.Arm64.UdivremFinal.udivrem_rem_L_final (L := 5) (by decide) (by decide))]
  rename_i hregs hq hrem hf
  (try simp only [setReg, reduceIte, Nat.reduceEqDiff, hr0, hr3, hr7, e144, e216, e248] at hf hrem)
  have hz8 : s'.mem.readLE (S.sp.toNat + 376) 8 = zv.toNat := by
    rw [hf.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hspill
  have hret' : s'.mem.readLE S.sp.toNat 8 = R.toNat := by
    rw [hf.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hret
  have hx29' : s'.mem.readLE (S.sp.toNat - 8) 8 = X29.toNat := by
    rw [hf.readLE _ _ (by simp only [Outside, and_true]; omega)]; exact hx29
  janus_run [hz8, hret', hx29', Util.readLE_32]
  refine ⟨?_, ?_⟩
  · simp only [Fv256.B.wv4_eq, Util.readLE_32, Nat.reducePow, Nat.add_assoc, Nat.reduceAdd] at hrem
    exact Fv256.AM.eq_mod_congr _ _ _ _ _ _ (by omega) (by omega) (by omega) hrem
  · janus_frame

end Fv256.Arm64.AddModSegE
