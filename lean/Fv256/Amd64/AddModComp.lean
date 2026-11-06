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
import Fv256.Amd64.AddModSegA
import Fv256.Amd64.AddModSegB
import Fv256.Amd64.AddModSegBc
import Fv256.Amd64.AddModSegZ
import Fv256.Amd64.AddModSegC
import Fv256.Amd64.AddModSegCov
import Fv256.Amd64.AddModSegD
import Fv256.Amd64.AddModSegE

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.AddModSpecS Fv256.SegCompose

namespace Fv256.Amd64.AddModComp

set_option hygiene false in
macro "omg" : tactic => `(tactic| (keep_only hlow hnw hdz hdm hdg hdgz hdd1 hdd2 hzm hgb; omega))

abbrev addmodEntry : Nat := segAddr Fv256.AddModProg.program "github.com/holiman/uint256.(*Int).AddMod"

-- the tail of the general path, from `0x296` (the add), for a pointer `S.regs 2` holding the modulus -/
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem tail (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x296))
    (hx15 : S.xmm 15 = 0) (hret : S.mem.readLE ((S.regs 4).toNat + 0x168) 8 < 2 ^ 47)
    (hdacc : S.mem.accessible 5184320 96 false = true) (hrod : S.mem.readLE 5184344 16 = 18446744073709551616)
    (hdd1 : (S.regs 4).toNat - 0x158 + 0x2e8 ≤ 5184320 ∨ 5184320 + 96 ≤ (S.regs 4).toNat - 0x158)
    (hdd2 : (S.regs 0).toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ (S.regs 0).toNat)
    (hlow : 0x1e8 ≤ (S.regs 4).toNat) (hnw : (S.regs 4).toNat + 0x190 ≤ 2 ^ 48)
    (hacc : S.mem.accessible ((S.regs 4).toNat - 0x1e0) 0x370 true = true)
    (hgl : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true)
    (hgn : (S.regs 14).toNat + 16 + 8 ≤ 2 ^ 48)
    (hgb : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 0x190 < (S.regs 4).toNat)
    (hz : Buffer S (S.regs 0) 32 true) (hx : Buffer S (S.regs 3) 32 false)
    (hy : Buffer S (S.regs 1) 32 false) (hm : Buffer S (S.regs 2) 32 false)
    (hdz : (S.regs 0).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 0).toNat)
    (hdm : (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 2).toNat)
    (hdg : (S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 14).toNat + 16)
    (hdgz : (S.regs 14).toNat + 24 ≤ (S.regs 0).toNat ∨ (S.regs 0).toNat + 32 ≤ (S.regs 14).toNat + 16)
    (hzx : S.regs 0 = S.regs 3 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 3).toNat ∨ (S.regs 3).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hzm : (S.regs 0).toNat + 32 ≤ (S.regs 2).toNat ∨ (S.regs 2).toNat + 32 ≤ (S.regs 0).toNat)
    (hmne : S.mem.readLE (S.regs 2).toNat 32 ≠ 0) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 0x168) 8)) S
      (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 0x170#64 ∧
        S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
        S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        S'.mem.readLE (S.regs 0).toNat 32 = Fv256.F.addmodSpec (S.mem.readLE (S.regs 3).toNat 32) (S.mem.readLE (S.regs 1).toNat 32) (S.mem.readLE (S.regs 2).toNat 32) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), ((S.regs 4).toNat - 0x1e0, (S.regs 4).toNat + 0x190)]) := by
  obtain ⟨hzw, hza⟩ := hz
  obtain ⟨hxw, hxa⟩ := hx
  obtain ⟨hyw, hya⟩ := hy
  obtain ⟨hmw, hma⟩ := hm
  by_cases hov : S.mem.readLE (S.regs 3).toNat 32 + S.mem.readLE (S.regs 1).toNat 32 < 2 ^ 256
  · refine seg_trans (Fv256.Amd64.AddModSegC.segC S hpc hzw hza hxw hxa hyw hya hzx hzy hov) (fun S3 hpc3 hq3 => ?_)
    obtain ⟨-, hreg3, hxmm3, hdf3, hmx3, hmf3, hval3⟩ := hq3
    have e0 : S3.regs 0 = S.regs 0 := hreg3 0 (by decide) (by decide)
    have e2 : S3.regs 2 = S.regs 2 := hreg3 2 (by decide) (by decide)
    have e4 : S3.regs 4 = S.regs 4 := hreg3 4 (by decide) (by decide)
    have e14 : S3.regs 14 = S.regs 14 := hreg3 14 (by decide) (by decide)
    have e5 : S3.regs 5 = S.regs 5 := hreg3 5 (by decide) (by decide)
    have hout : ∀ a n, (a + n ≤ (S.regs 0).toNat ∨ (S.regs 0).toNat + 32 ≤ a) → S3.mem.readLE a n = S.mem.readLE a n :=
      fun a n h => hmf3.readLE a n (by simp only [Janus.outside_cons, Janus.outside_nil, and_true]; exact h)
    have hS3 := Fv256.Amd64.AddModSegD.segD S3 hpc3 (by rw [hxmm3]; exact hx15)
      (by rw [e4, hout _ _ (by omg)]; exact hret) (by rw [e4]; exact hlow) (by rw [e4]; omg)
      (by rw [e4, hmf3.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omg) (by omg))
      (by rw [e14, hmf3.accessible]; exact hgl) (by rw [e14]; exact hgn)
      (by rw [e14, e4, hout _ _ (by omg)]; exact hgb)
      (by rw [e0]; exact ⟨hzw, by rw [hmf3.accessible]; exact hza⟩) (by rw [e2]; exact ⟨hmw, by rw [hmf3.accessible]; exact hma⟩)
      (by rw [e0, e4]; omg) (by rw [e2, e4]; omg) (by rw [e14, e4]; omg)
    have hrt : S3.mem.readLE ((S3.regs 4).toNat + 360) 8 = S.mem.readLE ((S.regs 4).toNat + 0x168) 8 := by
      rw [e4, hout _ _ (by omg)]
    rw [hrt] at hS3
    refine seg_mono hS3 ?_
    rintro S' ⟨r0, r4, r5, r14, rx, rdf, rmx, rval, rfr⟩
    rw [e0] at r0 rval rfr; rw [e4] at r4 r5 rfr; rw [e2] at rval; rw [e14] at r14
    refine ⟨r0, r4, ?_, r14, by rw [rx, hxmm3], by rw [rdf, hdf3], by rw [rmx, hmx3], ?_, ?_⟩
    · rw [r5, hout _ _ (by omg)]
    · rw [rval, hval3, hout _ _ (by omg)]; unfold Fv256.B.modSpec Fv256.F.addmodSpec; rfl
    · exact hmf3.trans rfr (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; keep_only h; omega)
  · have hov' : 2 ^ 256 ≤ S.mem.readLE (S.regs 3).toNat 32 + S.mem.readLE (S.regs 1).toNat 32 := Nat.not_lt.mp hov
    refine seg_trans (Fv256.Amd64.AddModSegCov.segCov S hpc hzw hza hxw hxa hyw hya hzx hzy hov') (fun S3 hpc3 hq3 => ?_)
    obtain ⟨-, hreg3, hxmm3, hdf3, hmx3, hmf3, hval3⟩ := hq3
    have e0 : S3.regs 0 = S.regs 0 := hreg3 0 (by decide) (by decide)
    have e2 : S3.regs 2 = S.regs 2 := hreg3 2 (by decide) (by decide)
    have e4 : S3.regs 4 = S.regs 4 := hreg3 4 (by decide) (by decide)
    have e14 : S3.regs 14 = S.regs 14 := hreg3 14 (by decide) (by decide)
    have hout : ∀ a n, (a + n ≤ (S.regs 0).toNat ∨ (S.regs 0).toNat + 32 ≤ a) → S3.mem.readLE a n = S.mem.readLE a n :=
      fun a n h => hmf3.readLE a n (by simp only [Janus.outside_cons, Janus.outside_nil, and_true]; exact h)
    have b0 := Util.readLE8_lt S.mem (S.regs 2).toNat
    have b1 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 8)
    have b2 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 16)
    have b3 := Util.readLE8_lt S.mem ((S.regs 2).toNat + 24)
    have hm0 := hmne
    have hmne4 : ¬ (S.mem.readLE (S.regs 2).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 2).toNat + 24) 8 = 0) := by
      rintro ⟨h0, h1, h2, h3⟩; apply hmne; rw [Util.readLE_32]; omega
    have hS3 := Fv256.Amd64.AddModSegE.segE S3 hpc3 (by rw [hxmm3]; exact hx15)
      (by rw [e4, hout _ _ (by omg)]; exact hret)
      (by rw [hmf3.accessible]; exact hdacc) (by rw [hout _ _ (by omg)]; exact hrod)
      (by rw [e4]; omg) (by rw [e0]; exact hdd2)
      (by rw [e4]; omg) (by rw [e4]; omg)
      (by rw [e4, hmf3.accessible]; exact Janus.Arm64.Memory.accessible_mono _ hacc (by omg) (by omg))
      (by rw [e14, hmf3.accessible]; exact hgl) (by rw [e14]; exact hgn)
      (by rw [e14, e4, hout _ _ (by omg)]; omg)
      (by rw [e0]; exact ⟨hzw, by rw [hmf3.accessible]; exact hza⟩) (by rw [e2]; exact ⟨hmw, by rw [hmf3.accessible]; exact hma⟩)
      (by rw [e2, hout _ _ (by omg), hout _ _ (by omg), hout _ _ (by omg), hout _ _ (by omg)]; exact hmne4)
      (by rw [e0, e4]; omg) (by rw [e2, e4]; omg) (by rw [e14, e4]; omg)
    have hrt : S3.mem.readLE ((S3.regs 4).toNat + 0x168) 8 = S.mem.readLE ((S.regs 4).toNat + 0x168) 8 := by
      rw [e4, hout _ _ (by omg)]
    rw [hrt] at hS3
    refine seg_mono hS3 ?_
    rintro S' ⟨r0, r4, r5, r14, rx, rdf, rmx, rval, rfr⟩
    rw [e0] at r0 rval rfr; rw [e4] at r4 r5 rfr; rw [e2] at rval; rw [e14] at r14
    refine ⟨r0, r4, ?_, r14, by rw [rx, hxmm3], by rw [rdf, hdf3], by rw [rmx, hmx3], ?_, ?_⟩
    · rw [r5, hout _ _ (by omg)]
    · rw [rval, hout (S.regs 2).toNat 32 (by omg), hval3]
      unfold Fv256.F.addmodSpec
      rw [if_neg hm0]
    · exact hmf3.trans rfr (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; keep_only h; omega)

end Fv256.Amd64.AddModComp
