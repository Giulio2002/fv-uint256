import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanBPre
import Fv256.Amd64.ScanBData
import Fv256.Amd64.ScanSfd
import Fv256.GrabLive
import Fv256.Amd64.ScanB1

/-!
# `Scan` (amd64), Level B segment: a `[]byte` source (`string(src)` through `runtime.slicebytetostring`, then the same call as for `string`)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanB

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Scan with a `[]byte` source -/
theorem scan_bytes (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsci : SciSumm (Extracted.program.link impl))
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s)
    (htw : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65») :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨h0, h3, h1, hlo, hhi, hcase⟩ := hpre
  have hdf : s.df = false := hret.2.2.2
  rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨hdw1, hdw2⟩, hdwo, hrtA, hav, htls, hPre, hPg⟩ | ⟨-, -, h, -⟩
  · exfalso; rw [h] at htw; exact absurd htw (by decide)
  · exfalso; exact absurd (h.symm.trans htw) (by decide)
  · have hty : Extracted.dataAddr.«type:[]uint8#7efbbf65» = 5002336 := by decide
    have hs3 : s.regs 3 = 5002336#64 := by
      rw [h3]; apply BitVec.eq_of_toNat_eq; rw [htw, hty]; rfl
    have hPre' := hPre
    obtain ⟨hP0, hP3, hP1, hMod, hEnv, hPlo, hPhi, hokD, hcost, hstW, hstR, hstP, hstZ, hmult, hmultR, hmultK, heofA, heofW, heofR,
      hbigA, hbigW, hbigR, hinit, hmaxA, hmaxW, hmaxR, hmaxB, hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hchunk⟩ := hPre'
    obtain ⟨e1', e2', e3, e4', e5', e6', e7', e8', e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
    have e4 : (s.regs 4).toNat % 8 = 0 := e4'
    have e13s : (s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 14).toNat + 16 := e13
    have e11s : Outside ((s.regs 14).toNat + 16) 8 R.rt := e11
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
    have hw4 : s.mem.accessible ((s.regs 4).toNat - 64 + 0x48) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
    have hdwb : dw.toNat + 24 ≤ 2 ^ 48 := hdw1
    have hs1 : s.regs 1 = dw := h1
    have hd1 : dw.toNat + 24 ≤ lo ∨ hi ≤ dw.toNat := by
      have := hdwo; simp only [outside_cons, outside_nil, and_true] at this; exact this
    have hhash : s.mem.readLE (5002336 + 16) 4 = 0x7efbbf65 := by have := Fv256.Amd64.ScanBData.hashB _ hdl; rw [hty] at this; exact this
    have hha : s.mem.accessible (5002336 + 16) 4 false = true := by have := Fv256.Amd64.ScanBData.accB _ hdl; rw [hty] at this; exact this
    have hdj := Fv256.Amd64.ScanBData.aprtB s.mem hdl e5
    have hdj2 : hi ≤ 5002336 ∨ 5002336 + 256 ≤ lo := by omega
    have hne : (5002336 : Nat) ≠ 0 := by decide
    have hdlH : Fv256.Amd64.ScanSfd.Hid (Extracted.program.DataLoaded s.mem) := hdl
    have hbuf : s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hdS1 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ (s.regs 4).toNat - 72 - 4096 ∨ (s.regs 4).toNat - 72 ≤ (hdrP s dw).toNat := by
      have := hiwin; omega
    have hdS2 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 40 ≤ (hdrP s dw).toNat := by
      have := hiwin; omega
    have hdA : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 40 + 32 ≤ (hdrP s dw).toNat := by
      have := hiwin; omega
    obtain ⟨hib1, hib2⟩ := hibuf
    have hib2' : s.mem.accessible (hdrP s dw).toNat (hdrN s dw).toNat false = true := hib2
    have e17s : R.inv b L (s.regs 14).toNat (view R.rt L s.mem) := e17
    have hPv : (hdrP s dw).toNat = s.mem.readLE dw.toNat 8 := by
      unfold hdrP; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.Util.readLE8_lt _ _)
    have hNv : (hdrN s dw).toNat = s.mem.readLE (dw.toNat + 8) 8 := by
      unfold hdrN; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.Util.readLE8_lt _ _)
    simp only [hPv, hNv] at hdS1 hdS2 hdA hib1 hib2' hokD hcost
    have hbuf' : (s.regs 4).toNat - 40 = 0 ∨ ((s.regs 4).toNat - 40 ≤ 281474976710624 ∧
        s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true) := Or.inr ⟨by omega, hbuf⟩
    have hs8 : ((s.regs 4).toNat - 72) % 8 = 0 := by omega
    have hib1' : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ 281474976710656 := by
      have : (2:Nat) ^ 48 = 281474976710656 := by decide
      omega
    have hdS3 : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ (s.regs 4).toNat - 72 + 8 ∨
        (s.regs 4).toNat - 72 + 8 + 24 ≤ s.mem.readLE dw.toNat 8 := by omega
    have hgm : (((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 5002336).writeLE
        ((s.regs 4).toNat + 24) 8 dw.toNat).writeLE ((s.regs 4).toNat + 8) 8 dst.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930331).readLE
        ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hg1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 72 - 4096 ∨ (s.regs 4).toNat - 72 ≤ (s.regs 14).toNat + 16 := by omega
    have hg2 : (s.regs 14).toNat + 16 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 72 + 16 ≤ (s.regs 14).toNat := by omega
    have hLsep : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++
          [((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)]) := by
      intro r hr
      have := e18 r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      omega
    have hPreH : Fv256.Amd64.ScanSfd.Hid (PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw))) := hPre
    clear hPre hP0 hP3 hP1 hMod hPlo hPhi hstW hstR hstP hstZ hmult hmultR hmultK heofA heofW heofR
      hbigA hbigW hbigR hinit hmaxA hmaxW hmaxR hmaxB hzbuf hzwin hzR hzP hzS hzg hchunk hib2 e15 e16 e17 e1' e2' e3 e4' e5' e6' e7' e8'
    run_tac Lean.logInfo m!"before run"
    janus64_run [hs3, hs1, hhash, hha, e7, e6, e8, hne, hs8, hbuf', hib1', hib2', hdS1, hdS2, hdS3, hdA, hgm, hg1, hg2, hLsep, hokD, hcost] until [sci] calls [hsb]
    all_goals trace_state
    all_goals sorry
  · exfalso; exact h htw
