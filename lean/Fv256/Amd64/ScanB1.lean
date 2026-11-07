import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanBPre
import Fv256.Amd64.ScanBData
import Fv256.Amd64.ScanA7

/-!
# `Scan` (amd64), Level B segment: a `string` source
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanB

/-- the summary of `scanScientificFromString` (Level A), as a callee summary at its entry -/
def SciSumm (P : Janus.Amd64.Program) : Prop :=
  ∀ (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64),
    Summary P sci (fun s => SciPre cfg avxAddr R R2 T b L lo hi dst p n s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => SciPost cfg R R2 b L lo hi dst p n s s')

set_option maxRecDepth 100000 in
/-- Scan with a `string` source -/
theorem scan_str (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hsci : SciSumm (Extracted.program.link impl))
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s)
    (htw : tw.toNat = Extracted.dataAddr.«type:string#f88732b8») :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨h0, h3, h1, hlo, hhi, hcase⟩ := hpre
  have hdf : s.df = false := hret.2.2.2
  rcases hcase with ⟨h, -⟩ | ⟨-, ⟨hdw1, hdw2⟩, hdwo, hav, htls, hTop, hpg⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
  · exfalso; rw [h] at htw; exact absurd htw (by decide)
  · have hty : Extracted.dataAddr.«type:string#f88732b8» = 5008128 := by decide
    have hs3 : s.regs 3 = 5008128#64 := by
      rw [h3]; apply BitVec.eq_of_toNat_eq; rw [htw, hty]; rfl
    have hEnv := hTop.env
    obtain ⟨e1', e2', e3, e4', e5', e6', e7', e8', -⟩ := hEnv
    have e5 : s.mem.accessible lo (hi - lo) true = true := e5'
    have e6 : (s.regs 14).toNat + 24 ≤ 2 ^ 48 := e6'
    have e7 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := e7'
    have e8 : s.mem.readLE ((s.regs 14).toNat + 16) 8 < lo := e8'
    have hsp := (s.regs 4).isLt
    have hw1 : s.mem.accessible ((s.regs 4).toNat - 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hw2 : s.mem.accessible ((s.regs 4).toNat + 16) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hw3 : s.mem.accessible ((s.regs 4).toNat + 24) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hw4 : s.mem.accessible ((s.regs 4).toNat - 72) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
    have hdwb : dw.toNat + 16 ≤ 2 ^ 48 := hdw1
    have hs1 : s.regs 1 = dw := h1
    have hd1 : dw.toNat + 16 ≤ lo ∨ hi ≤ dw.toNat := by
      have := hdwo; simp only [outside_cons, outside_nil, and_true] at this; exact this
    have hhash : s.mem.readLE (5008128 + 16) 4 = 0xf88732b8 := by have := Fv256.Amd64.ScanBData.hashS _ hdl; rw [hty] at this; exact this
    have hha : s.mem.accessible (5008128 + 16) 4 false = true := by have := Fv256.Amd64.ScanBData.accS _ hdl; rw [hty] at this; exact this
    have hdj := Fv256.Amd64.ScanBData.aprtS s.mem hdl e5
    have hdj2 : hi ≤ 5008128 ∨ 5008128 + 384 ≤ lo := by omega
    have hdj3 : hi ≤ 5008128 ∨ 5008128 + 384 ≤ lo := hdj2
    have hTopH : Fv256.Amd64.ScanSfd.Hid (TopPre0 cfg R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw))) := hTop
    have hdlH : Fv256.Amd64.ScanSfd.Hid (Extracted.program.DataLoaded s.mem) := hdl
    have hne : (5008128 : Nat) ≠ 0 := by decide
    clear hTop hdl e1' e2' e3 e4' e5' e6' e7' e8'
    janus64_run [hs3, hs1, hhash, hha, e7, e6, e8, hne] until [sci]
    refine ReachesRet.call_regions (hsci R R2 T b L lo ((s.regs 4).toNat - 40) dst (hdrP s dw) (hdrN s dw)) rfl ?_ ?_
    · have hlo' : lo ≤ (s.regs 4).toNat := by omega
      refine ⟨Fv256.Amd64.ScanBPre.sciPre_str cfg hTopH hlo ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htls, ?_⟩
      · refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
      · rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by decide)
      · simp [setRegF_apply]
      · simpa [setRegF_apply] using h0
      · simp [setRegF_apply, hdrP]
      · simp [setRegF_apply, hdrN]
      · simp [setRegF_apply]
      · simpa using hret.2.2.1
      · simpa using hdf
      · simp
      · exact hav
      · exact hpg
      · have hdl' : Extracted.program.DataLoaded s.mem := hdlH
        refine Fv256.Amd64.ScanSfd.dl_frame hdl' (by simp) ?_ (rs := [(lo, hi)]) (by simp; omega) (by simpa using e5)
        refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    · intro S' hr hq hreg
      obtain ⟨hK, hSP, hMF⟩ := hq
      obtain ⟨k1, k4, k5, k14, kx, kdf, kfs⟩ := hK
      have hdl' : Extracted.program.DataLoaded s.mem := hdlH
      have hT := hTopH
      have hEnv := hT.env
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, -⟩ := hEnv
      have f9' : Outside lo (hi - lo) R.rt := f9
      have f10' : Outside lo (hi - lo) R2.priv := f10
      have hsp := (s.regs 4).isLt
      have hs4 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      have hrip : S'.rip = BitVec.ofNat 64 4930385 := by
        rw [k1]; simp only [retAddrOf, setRegF_apply]
        simp only [show (4 = 5) = False from by decide, if_false, if_true]
        rw [hs4, Janus.Arm64.Memory.readLE_writeLE_self]
      have hr4' : S'.regs 4 = s.regs 4 - 64#64 := by
        rw [k4]; simp only [setRegF_apply]
        simp only [show (4 = 5) = False from by decide, if_false, if_true]
        bv_omega
      have hr5' : S'.regs 5 = s.regs 4 - 8#64 := by
        rw [k5]; simp [setRegF_apply]
      have hzw : dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat := hT.zwin
      have hhi32 : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
      have ho8 : Outside ((s.regs 4).toNat - 8) 8 (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (dst.toNat, dst.toNat + 32)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
        refine ⟨⟨Outside.of_sub f9' (by omega) (by omega), Outside.of_sub f10' (by omega) (by omega)⟩, by omega, by omega⟩
      have ho0 : Outside (s.regs 4).toNat 8 (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (dst.toNat, dst.toNat + 32)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
        refine ⟨⟨Outside.of_sub f9' (by omega) (by omega), Outside.of_sub f10' (by omega) (by omega)⟩, by omega, by omega⟩
      have hm8 : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [hMF.readLE _ _ ho8]
        have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this)
      have hm0 : S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [hMF.readLE _ _ ho0]
        have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      have ha8 : S'.mem.accessible ((s.regs 4).toNat - 8) 8 false = true := by
        rw [hMF.accessible]
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
      have ha0 : S'.mem.accessible (s.regs 4).toNat 8 false = true := by
        rw [hMF.accessible]
        simp only [Janus.Arm64.Memory.accessible_writeLE]
        exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
      janus64_run [hm8, hm0, ha8, ha0]
      have hpost := Fv256.Amd64.ScanBPre.post_str cfg hTopH ?hF1 hSP hMF
      refine ⟨?_, Or.inr (Or.inl ⟨htw, hpost.1, hpost.2⟩)⟩
      · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · simpa [setRegF_apply] using k14
        · exact kx
        · simp [hdf]
        · show S'.fsBase = s.fsBase
          rw [kfs]
      case hF1 =>
        refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  · exfalso; exact absurd (htw.symm.trans h) (by decide)
  · exfalso; exact h htw
