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
macro "omg" : tactic => `(tactic| (keep_only hlow hnw hdz hdx hdy hdm hdg hdgz hdd1 hdd2 hzm hgb; omega))

set_option hygiene false in
macro "omgs" : tactic => `(tactic| (keep_only hsp hlow hnw hdz hdx hdy hdm hdg hdgz h_ddisj0_0 h_ddisj1_0 hgb; omega))

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
    (hdm : (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 2).toNat ∨
      ((S.regs 4).toNat + 0x140 ≤ (S.regs 2).toNat ∧ (S.regs 2).toNat + 32 ≤ (S.regs 4).toNat + 0x170))
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

-- the general path from `0x235` (after the prologue)
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
theorem mid (S : State) (hpc : S.rip = BitVec.ofNat 64 (addmodEntry + 0x235))
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
    (hy : Buffer S (S.regs 1) 32 false) (hm : Buffer S (S.regs 7) 32 false)
    (hdz : (S.regs 0).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 0).toNat)
    (hdx : (S.regs 3).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 3).toNat)
    (hdy : (S.regs 1).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 1).toNat)
    (hdm : (S.regs 7).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 7).toNat)
    (hdg : (S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S.regs 14).toNat + 16)
    (hdgz : (S.regs 14).toNat + 24 ≤ (S.regs 0).toNat ∨ (S.regs 0).toNat + 32 ≤ (S.regs 14).toNat + 16)
    (hzx : S.regs 0 = S.regs 3 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 3).toNat ∨ (S.regs 3).toNat + 32 ≤ (S.regs 0).toNat)
    (hzy : S.regs 0 = S.regs 1 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 1).toNat ∨ (S.regs 1).toNat + 32 ≤ (S.regs 0).toNat)
    (hzm : S.regs 0 = S.regs 7 ∨ (S.regs 0).toNat + 32 ≤ (S.regs 7).toNat ∨ (S.regs 7).toNat + 32 ≤ (S.regs 0).toNat)
    (hr2 : S.regs 2 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 7).toNat + 24) 8)) :
    ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 0x168) 8)) S
      (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 0x170#64 ∧
        S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
        S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
        S'.mem.readLE (S.regs 0).toNat 32 = Fv256.F.addmodSpec (S.mem.readLE (S.regs 3).toNat 32) (S.mem.readLE (S.regs 1).toNat 32) (S.mem.readLE (S.regs 7).toNat 32) ∧
        MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), ((S.regs 4).toNat - 0x1e0, (S.regs 4).toNat + 0x190)]) := by
  have b0 := Util.readLE8_lt S.mem (S.regs 7).toNat
  have b1 := Util.readLE8_lt S.mem ((S.regs 7).toNat + 8)
  have b2 := Util.readLE8_lt S.mem ((S.regs 7).toNat + 16)
  have b3 := Util.readLE8_lt S.mem ((S.regs 7).toNat + 24)
  by_cases hm0 : S.mem.readLE (S.regs 7).toNat 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 8) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 16) 8 = 0 ∧ S.mem.readLE ((S.regs 7).toNat + 24) 8 = 0
  · have hacc2 : S.mem.accessible ((S.regs 4).toNat + 0x150) 0x20 true = true :=
      Janus.Arm64.Memory.accessible_mono _ hacc (by omg) (by omg)
    have hz0 := Fv256.Amd64.AddModSegZ.segZ S hpc hx15 hret hacc2 (by omg) hz hm hr2 hm0 (by omg)
    refine seg_mono hz0 ?_
    rintro S' ⟨r0, r4, r5, r14, rx, rdf, rmx, rval, rfr⟩
    refine ⟨r0, r4, r5, r14, rx, rdf, rmx, ?_, ?_⟩
    · rw [rval]; unfold Fv256.F.addmodSpec
      have : S.mem.readLE (S.regs 7).toNat 32 = 0 := by
        rw [Util.readLE_32]; omega
      rw [this]; simp
    · exact rfr.mono (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; keep_only h; omega)
  · have step : ∀ S2 : State, S2.rip = BitVec.ofNat 64 (addmodEntry + 0x296) →
        (∀ i, i ≠ 2 → i ≠ 11 → S2.regs i = S.regs i) → S2.xmm = S.xmm → S2.df = S.df → S2.mxcsr = S.mxcsr →
        MemFrame S.mem S2.mem [((S.regs 4).toNat + 0x140, (S.regs 4).toNat + 0x160)] →
        ((S2.regs 2).toNat + 32 ≤ 2 ^ 48 ∧ S2.mem.accessible (S2.regs 2).toNat 32 false = true) →
        S2.mem.readLE (S2.regs 2).toNat 32 = S.mem.readLE (S.regs 7).toNat 32 →
        ((S2.regs 2).toNat + 32 ≤ (S.regs 4).toNat - 0x1e0 ∨ (S.regs 4).toNat + 0x190 ≤ (S2.regs 2).toNat ∨
          ((S.regs 4).toNat + 0x140 ≤ (S2.regs 2).toNat ∧ (S2.regs 2).toNat + 32 ≤ (S.regs 4).toNat + 0x170)) →
        ((S.regs 0).toNat + 32 ≤ (S2.regs 2).toNat ∨ (S2.regs 2).toNat + 32 ≤ (S.regs 0).toNat) →
        ReachesRet Fv256.AddModProg.program (BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 0x168) 8)) S2
          (fun S' => S'.regs 0 = S.regs 0 ∧ S'.regs 4 = S.regs 4 + 0x170#64 ∧
            S'.regs 5 = BitVec.ofNat 64 (S.mem.readLE ((S.regs 4).toNat + 352) 8) ∧ S'.regs 14 = S.regs 14 ∧
            S'.xmm 15 = S.xmm 15 ∧ S'.df = S.df ∧ S'.mxcsr = S.mxcsr ∧
            S'.mem.readLE (S.regs 0).toNat 32 = Fv256.F.addmodSpec (S.mem.readLE (S.regs 3).toNat 32) (S.mem.readLE (S.regs 1).toNat 32) (S.mem.readLE (S.regs 7).toNat 32) ∧
            MemFrame S.mem S'.mem [((S.regs 0).toNat, (S.regs 0).toNat + 32), ((S.regs 4).toNat - 0x1e0, (S.regs 4).toNat + 0x190)]) := by
      intro S2 hpc2 hreg2 hxmm2 hdf2 hmx2 hfr2 hm2 hmz hdm2 hzm2
      have e0 : S2.regs 0 = S.regs 0 := hreg2 0 (by decide) (by decide)
      have e1 : S2.regs 1 = S.regs 1 := hreg2 1 (by decide) (by decide)
      have e3 : S2.regs 3 = S.regs 3 := hreg2 3 (by decide) (by decide)
      have e4 : S2.regs 4 = S.regs 4 := hreg2 4 (by decide) (by decide)
      have e14 : S2.regs 14 = S.regs 14 := hreg2 14 (by decide) (by decide)
      have hout2 : ∀ a n, (a + n ≤ (S.regs 4).toNat + 0x140 ∨ (S.regs 4).toNat + 0x160 ≤ a) → S2.mem.readLE a n = S.mem.readLE a n :=
        fun a n h => hfr2.readLE a n (by simp only [Janus.outside_cons, Janus.outside_nil, and_true]; exact h)
      have hmne : S2.mem.readLE (S2.regs 2).toNat 32 ≠ 0 := by
        rw [hmz]; intro h; apply hm0; rw [Util.readLE_32] at h; keep_only b0 b1 b2 b3 h; omega
      have ht := tail S2 hpc2 (by rw [hxmm2]; exact hx15)
        (by rw [e4, hout2 _ _ (by omg)]; exact hret)
        (by rw [hfr2.accessible]; exact hdacc) (by rw [hout2 _ _ (by omg)]; exact hrod)
        (by rw [e4]; exact hdd1) (by rw [e0]; exact hdd2)
        (by rw [e4]; exact hlow) (by rw [e4]; exact hnw)
        (by rw [e4, hfr2.accessible]; exact hacc)
        (by rw [e14, hfr2.accessible]; exact hgl) (by rw [e14]; exact hgn)
        (by rw [e14, e4, hout2 _ _ (by omg)]; exact hgb)
        (by rw [e0]; exact ⟨hz.1, by rw [hfr2.accessible]; exact hz.2⟩)
        (by rw [e3]; exact ⟨hx.1, by rw [hfr2.accessible]; exact hx.2⟩)
        (by rw [e1]; exact ⟨hy.1, by rw [hfr2.accessible]; exact hy.2⟩) hm2
        (by rw [e0, e4]; exact hdz) (by rw [e4]; exact hdm2) (by rw [e14, e4]; exact hdg) (by rw [e14, e0]; exact hdgz)
        (by rw [e0, e3]; exact hzx) (by rw [e0, e1]; exact hzy) (by rw [e0]; exact hzm2) hmne
      have hrt : S2.mem.readLE ((S2.regs 4).toNat + 0x168) 8 = S.mem.readLE ((S.regs 4).toNat + 0x168) 8 := by
        rw [e4, hout2 _ _ (by omg)]
      rw [hrt] at ht
      refine seg_mono ht ?_
      rintro S' ⟨r0, r4, r5, r14, rx, rdf, rmx, rval, rfr⟩
      rw [e0] at r0 rval rfr; rw [e4] at r4 r5 rfr; rw [e14] at r14
      refine ⟨r0, r4, ?_, r14, by rw [rx, hxmm2], by rw [rdf, hdf2], by rw [rmx, hmx2], ?_, ?_⟩
      · rw [r5, hout2 _ _ (by omg)]
      · rw [rval, e3, e1, hmz, hout2 _ _ (by omg), hout2 _ _ (by omg)]
      · exact hfr2.trans rfr (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; keep_only h hlow; omega)
    have hmr := hm.1
    have hma := hm.2
    by_cases ha : S.regs 7 = S.regs 0
    · have hsa : S.mem.accessible ((S.regs 4).toNat + 0x140) 32 true = true :=
        Janus.Arm64.Memory.accessible_mono _ hacc (by omg) (by omg)
      have hsa' := Janus.Arm64.Memory.accessible_read_of_write _ hsa
      refine seg_trans (Fv256.Amd64.AddModSegBc.segBc S hpc hm0 ha hx15 hmr hma hsa (by omg) (by omg) hr2) (fun S2 hpc2 hq2 => ?_)
      obtain ⟨-, r2, hreg2, hxmm2, hdf2, hmx2, hfr2, hcl⟩ := hq2
      have r2n : (S2.regs 2).toNat = (S.regs 4).toNat + 0x140 := by
        rw [r2, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
      exact step S2 hpc2 hreg2 hxmm2 hdf2 hmx2 hfr2 ⟨by rw [r2n]; omega, by rw [r2n, hfr2.accessible]; exact hsa'⟩
        (by rw [r2n]; exact hcl) (by rw [r2n]; omega) (by rw [r2n]; omg)
    · have hne7 : S.regs 7 ≠ S.regs 0 := ha
      refine seg_trans (Fv256.Amd64.AddModSegB.segB S hpc hm0 hne7 hmr hma hr2) (fun S2 hpc2 hq2 => ?_)
      obtain ⟨-, r2, hreg2, hxmm2, hdf2, hmx2, hfr2⟩ := hq2
      have hmem : S2.mem = S.mem := hfr2
      have hzm' : (S.regs 0).toNat + 32 ≤ (S.regs 7).toNat ∨ (S.regs 7).toNat + 32 ≤ (S.regs 0).toNat := by
        rcases hzm with h | h | h
        · exact absurd h.symm ha
        · exact Or.inl h
        · exact Or.inr h
      refine step S2 hpc2 ?_ hxmm2 hdf2 hmx2 (by rw [hmem]; exact MemFrame.refl _ _) ?_ ?_ ?_ ?_
      · exact hreg2
      · rw [r2, hmem]; exact ⟨hmr, hma⟩
      · rw [hmem, r2]
      · rw [r2]; omg
      · rw [r2]; exact hzm'

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem gen2 :
    Summary Fv256.AddModProg.program addmodEntry (fun s => AddPre Fv256.AddModProg.program s ∧ ¬ AddCase s) AddPost := by
  intro s hpc ⟨hpre, hnc⟩
  have hA := Fv256.Amd64.AddModSegA.segA s hpc hpre hnc
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hdata, hx15, ⟨hzw, hza⟩, ⟨hxw, hxa⟩, ⟨hyw, hya⟩, ⟨hmw, hma⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩ := hpre
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdgz
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hsp
  janus64_data hdata [hacc, hza]
  have hrod : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
  refine seg_trans hA (fun S1 hpc1 hq1 => ?_)
  obtain ⟨-, r4, r5, r2, hreg, hxmm, hdf, hmx, hmem⟩ := hq1
  have e0 : S1.regs 0 = s.regs 0 := hreg 0 (by decide) (by decide) (by decide) (by decide)
  have e1 : S1.regs 1 = s.regs 1 := hreg 1 (by decide) (by decide) (by decide) (by decide)
  have e3 : S1.regs 3 = s.regs 3 := hreg 3 (by decide) (by decide) (by decide) (by decide)
  have e7 : S1.regs 7 = s.regs 7 := hreg 7 (by decide) (by decide) (by decide) (by decide)
  have e14 : S1.regs 14 = s.regs 14 := hreg 14 (by decide) (by decide) (by decide) (by decide)
  have h4 : (S1.regs 4).toNat = (s.regs 4).toNat - 360 := by
    rw [r4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hrd : ∀ a n, (a + n ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat ≤ a) → S1.mem.readLE a n = s.mem.readLE a n := by
    intro a n h; rw [hmem]; exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  have hac : ∀ a n w, S1.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [hmem]; simp
  have hmid := mid S1 hpc1 (by rw [hxmm]; exact hx15)
    (by rw [h4, show (s.regs 4).toNat - 360 + 0x168 = (s.regs 4).toNat by omega, hrd _ _ (by omgs)]; exact hra2)
    (by rw [hac]; exact h_data0) (by rw [hrd _ _ (by omgs)]; exact hrod)
    (by rw [h4]; omgs) (by rw [e0]; exact h_ddisj1_0) (by rw [h4]; omgs) (by rw [h4]; omgs)
    (by rw [h4, hac, show (s.regs 4).toNat - 360 - 0x1e0 = (s.regs 4).toNat - 840 by omega]; exact hacc)
    (by rw [e14, hac]; exact hgr) (by rw [e14]; exact hnw2)
    (by rw [e14, h4, hrd _ _ (by omgs)]; omgs)
    (by rw [e0]; exact ⟨hzw, by rw [hac]; exact hza⟩) (by rw [e3]; exact ⟨hxw, by rw [hac]; exact hxa⟩)
    (by rw [e1]; exact ⟨hyw, by rw [hac]; exact hya⟩) (by rw [e7]; exact ⟨hmw, by rw [hac]; exact hma⟩)
    (by rw [e0, h4]; omgs) (by rw [e3, h4]; omgs) (by rw [e1, h4]; omgs) (by rw [e7, h4]; omgs)
    (by rw [e14, h4]; omgs) (by rw [e14, e0]; exact hdgz)
    (by rw [e0, e3]; exact hzx) (by rw [e0, e1]; exact hzy) (by rw [e0, e7]; exact hzm)
    (by rw [r2, e7, hrd _ _ (by omgs)])
  have hrt : BitVec.ofNat 64 (S1.mem.readLE ((S1.regs 4).toNat + 0x168) 8) = retAddrOf s := by
    rw [retAddrOf_eq, h4, show (s.regs 4).toNat - 360 + 0x168 = (s.regs 4).toNat by omega, hrd _ _ (by omgs)]
  rw [hrt] at hmid
  refine seg_mono hmid ?_
  rintro S' ⟨q0, q4, q5, q14, qx, qdf, qmx, qval, qfr⟩
  rw [e0] at q0 qval qfr; rw [e14] at q14
  rw [e1] at qval; rw [e3] at qval; rw [e7] at qval
  rw [h4] at qfr q5
  have hfr1 : MemFrame s.mem S1.mem [((s.regs 4).toNat - 8, (s.regs 4).toNat)] := by
    rw [hmem]; exact MemFrame.of_writeLE _ _ (List.mem_singleton_self _) (Nat.le_refl _) (by omega)
  refine ⟨q0, ?_, ?_, q14, by rw [qx, hxmm], by rw [qdf, hdf], by rw [qmx, hmx], ?_, ?_⟩
  · rw [q4, r4]; bv_omega
  · rw [q5, show (s.regs 4).toNat - 360 + 352 = (s.regs 4).toNat - 8 by omega, hmem, Janus.Arm64.Memory.readLE_writeLE_self]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  · rw [qval, hrd _ _ (by omgs), hrd _ _ (by omgs), hrd _ _ (by omgs)]
  · exact hfr1.trans qfr (by intro a n h; simp only [Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢; keep_only h hsp; omega)

end Fv256.Amd64.AddModComp
