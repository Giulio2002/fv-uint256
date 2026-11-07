import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanBPre
import Fv256.Amd64.ScanBData
import Fv256.Amd64.ScanSfd
import Fv256.GrabLive
import Fv256.Amd64.ScanB1
import Fv256.Amd64.ScanB2b
import Fv256.Amd64.ScanBSb
import Fv256.Amd64.ScanB2c

/-!
# `Scan` (amd64), Level B segment: a `[]byte` source (`string(src)` through `runtime.slicebytetostring`, then the same call as for `string`)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanB


/-- the state at the entry of `runtime.slicebytetostring` (called from `Scan`'s `[]byte` path) -/
def AtSb (s : State) (dst dw : BitVec 64) (S0 : State) : Prop :=
  S0.rip = BitVec.ofNat 64 sbAddr ∧ S0.regs 0 = s.regs 4 - 40#64 ∧ S0.regs 1 = hdrN s dw ∧ S0.regs 3 = hdrP s dw ∧
  S0.regs 4 = s.regs 4 - 72#64 ∧ S0.regs 5 = s.regs 4 - 8#64 ∧ S0.regs 14 = s.regs 14 ∧ S0.xmm 15 = s.xmm 15 ∧
  S0.df = s.df ∧ S0.fsBase = s.fsBase ∧
  S0.mem = ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 5002336).writeLE
    ((s.regs 4).toNat + 24) 8 dw.toNat).writeLE ((s.regs 4).toNat + 8) 8 dst.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930331

set_option maxRecDepth 100000 in
/-- Scan, `[]byte` source: the prefix up to the call of `slicebytetostring` -/
theorem bytes_seg1 (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (impl : List Janus.Amd64.Segment)
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (Q : State → Prop) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem) (hEnv : Env cfg R R2 T b L lo hi s)
    (hlo : lo + 4992 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (h0 : s.regs 0 = dst) (h3 : s.regs 3 = tw) (h1 : s.regs 1 = dw) (htw : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65»)
    (hdw1 : dw.toNat + 24 ≤ 2 ^ 48) (hdw2 : s.mem.accessible dw.toNat 24 false = true) (hdwo : Outside dw.toNat 24 [(lo, hi)])
    (hk : ∀ S0, AtSb s dst dw S0 → ReachesRet (Extracted.program.link impl) (retAddrOf s) S0 Q) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s Q := by
  have hty : Extracted.dataAddr.«type:[]uint8#7efbbf65» = 5002336 := by decide
  have hs3 : s.regs 3 = 5002336#64 := by
    rw [h3]; apply BitVec.eq_of_toNat_eq; rw [htw, hty]; rfl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, -⟩ := hEnv
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
  clear hdl
  have h0' := h0
  janus64_run [hs3, hs1, hhash, hha, e7, e6, e8, hne] until [sbAddr]
  exact hk _ ⟨rfl, by simp [setRegF_apply], by simp [setRegF_apply, hdrN], by simp [setRegF_apply, hdrP], by simp [setRegF_apply],
    by simp [setRegF_apply], by simp [setRegF_apply], rfl, rfl, rfl, by simp [h0]⟩

set_option maxRecDepth 100000 in
/-- the call of `slicebytetostring` from `Scan`, stated over the abstract entry state `S0` (no store chain in the context): the callee
precondition `hP` is an explicit hypothesis (proved by `sb_pre`); the continuation `hk` receives the results of the contract and the
state at the entry of `scanScientificFromString` -/
theorem bytes_call2 (impl : List Janus.Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (s S0 : State) (dw dst : BitVec 64) (Q : State → Prop)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hrip : S0.rip = BitVec.ofNat 64 sbAddr)
    (hP : RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b S0)
    (hargs : argWords64 S0 3 = [(s.regs 4).toNat - 40, (hdrP s dw).toNat, (hdrN s dw).toNat])
    (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 72)
    (hstr : strBytes S0.mem (hdrP s dw).toNat (hdrN s dw).toNat = strBytes s.mem (hdrP s dw).toNat (hdrN s dw).toNat)
    (hreg0 : S0.mem.regions = s.mem.regions) (hr14 : S0.regs 14 = s.regs 14)
    (hr4 : S0.regs 4 = s.regs 4 - 72#64) (hr5 : S0.regs 5 = s.regs 4 - 8#64) (hx : S0.xmm 15 = s.xmm 15)
    (hdf0 : S0.df = s.df) (hfs : S0.fsBase = s.fsBase) (hxs : s.xmm 15 = 0) (hds : s.df = false)
    (hra : S0.mem.readLE (S0.regs 4).toNat 8 = 4930331)
    (hacc8 : S0.mem.accessible ((s.regs 4).toNat - 72) 88 true = true)
    (hk : ∀ (S3 : State) (m M0 : Janus.Arm64.Memory) (r0 r1 : BitVec 64),
      Fv256.Amd64.ScanBSb.SbPost R stAddr b L s (hdrP s dw) (hdrN s dw) r0 r1 M0 m ((s.regs 4).toNat - 40) →
      M0 = S0.mem → S3.rip = BitVec.ofNat 64 sci → S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8) → S3.regs 3 = r0 → S3.regs 1 = r1 →
      S3.regs 4 = s.regs 4 - 72#64 → S3.regs 5 = s.regs 4 - 8#64 → S3.regs 14 = s.regs 14 → S3.xmm 15 = 0 → S3.df = false →
      S3.fsBase = s.fsBase → S3.mem = m.writeLE ((s.regs 4).toNat - 72) 8 4930347 → m.regions = s.mem.regions →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S3 Q) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S0 Q := by
  refine ReachesRet.call_regions (hsb L b) hrip hP ?_
  intro s' hr hq hreg
  obtain ⟨r0, r1, r2, junk, f, x, yh, m, zh, kr, hs', hSb⟩ :=
    Fv256.Amd64.ScanB.sb_post R L b s S0 s' _ _ _ hargs rfl hsp0 hstr hreg0 hr14 hq
  subst hs'
  have hret : retAddrOf S0 = 4930331#64 := by
    unfold retAddrOf; rw [hra]
  have hacm : m.accessible ((s.regs 4).toNat - 72) 88 true = true := by rw [hSb.mf.accessible]; exact hacc8
  have hregc := hreg
  clear hq hreg
  have hsp8 : (s.regs 4).toNat < 2 ^ 64 := (s.regs 4).isLt
  janus64_run [hret, hr4, hr5, hr14, hx, hdf0, hfs, hacm] until [sci]
  exact hk _ m S0.mem r0 r1 hSb rfl (by first | rfl | decide) (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14]) (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14]) (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14])
    (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14]) (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14]) (by simp [setRegF_apply, callRegs64_apply, hr4, hr5, hr14]) (by simp [hxs, hx]) (by simp [hds, hdf0]) (by simp [hfs])
    rfl (hregc.trans hreg0)

set_option maxRecDepth 100000 in
/-- Scan, `[]byte` source: the call of `slicebytetostring`, then `bytes_tail` -/
theorem bytes_call (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s S0 : State) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hsci : SciSumm (Extracted.program.link impl) R R2 T)
    (htw : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65»)
    (hPreV : PreB cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) (viewS s (hdrP s dw) (hdrN s dw)))
    (hav : s.mem.accessible avxAddr 1 false = true) (hPg : PagesB R stAddr lo hi s.mem)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone cfg R2 s.mem ∧
      Outside (s.fsBase.toNat - 8) 8 R.rt)
    (hrtA : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hAt : AtSb s dst dw S0) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S0
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨hrip, hr0, hr1, hr3, hr4, hr5, hr14, hx, hdf0, hfs, hmem⟩ := hAt
  have hPre : Fv256.Amd64.ScanBSb.PreBS cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s :=
    Fv256.Amd64.ScanBSb.PreBS.of cfg hPreV
  have hPre2 := hPre
  obtain ⟨hMod, hEnv, hPlo, hPhi, hokD, hcost, hstW, hstR, hstP, hstZ, hmult, hmultR, hmultK, heofA, heofW, heofR,
    hbigA, hbigW, hbigR, hinit, hmaxA, hmaxW, hmaxR, hmaxB, hzbuf, hzwin, hzR, hzP, hzS, hzg, hibuf, hiwin, hchunk⟩ := hPre2
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hsp := (s.regs 4).isLt
  have hbuf : s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true :=
    Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
  have hPv : (hdrP s dw).toNat = s.mem.readLE dw.toNat 8 := by
    unfold hdrP; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.Util.readLE8_lt _ _)
  have hNv : (hdrN s dw).toNat = s.mem.readLE (dw.toNat + 8) 8 := by
    unfold hdrN; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Fv256.Util.readLE8_lt _ _)
  obtain ⟨hib1, hib2⟩ := hibuf
  have hiw := hiwin
  have hdS1 : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ (s.regs 4).toNat - 72 - 4096 ∨ (s.regs 4).toNat - 72 ≤ s.mem.readLE dw.toNat 8 := by
    rw [hPv, hNv] at hiw; omega
  have hdS2 : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ (s.regs 4).toNat - 64 ∨ (s.regs 4).toNat - 40 ≤ s.mem.readLE dw.toNat 8 := by
    rw [hPv, hNv] at hiw; omega
  have hdS3 : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ (s.regs 4).toNat - 72 + 8 ∨
      (s.regs 4).toNat - 72 + 8 + 24 ≤ s.mem.readLE dw.toNat 8 := by
    rw [hPv, hNv] at hiw; omega
  have hdA : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 40 + 32 ≤ s.mem.readLE dw.toNat 8 := by
    rw [hPv, hNv] at hiw; omega
  have hib2' : s.mem.accessible (s.mem.readLE dw.toNat 8) (s.mem.readLE (dw.toNat + 8) 8) false = true := by
    rw [← hPv, ← hNv]; exact hib2
  have hib1' : s.mem.readLE dw.toNat 8 + s.mem.readLE (dw.toNat + 8) 8 ≤ 281474976710656 := by
    rw [← hPv, ← hNv]; have : (2:Nat) ^ 48 = 281474976710656 := by decide
    omega
  have hokD' : R.ok sbAddr [(s.regs 4).toNat - 40, s.mem.readLE dw.toNat 8, s.mem.readLE (dw.toNat + 8) 8] := by
    rw [← hPv, ← hNv]; exact hokD
  have hcost' : roundupsize (s.mem.readLE (dw.toNat + 8) 8) true ≤ b := by rw [← hNv]; exact hcost
  have hbuf' : (s.regs 4).toNat - 40 = 0 ∨ ((s.regs 4).toNat - 40 ≤ 281474976710624 ∧
      s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true) := Or.inr ⟨by omega, hbuf⟩
  have hs8 : ((s.regs 4).toNat - 72) % 8 = 0 := by omega
  have hgm : (S0.mem.readLE ((s.regs 14).toNat + 16) 8) = s.mem.readLE ((s.regs 14).toNat + 16) 8 := by
    rw [hmem]; simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hg1 : (s.regs 14).toNat + 16 + 8 ≤ (s.regs 4).toNat - 72 - 4096 ∨ (s.regs 4).toNat - 72 ≤ (s.regs 14).toNat + 16 := by omega
  have hg2 : (s.regs 14).toNat + 16 ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 72 + 16 ≤ (s.regs 14).toNat := by omega
  have hLsep : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
      ([((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++
        [((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)]) := by
    intro r hr
    have := e18 r hr
    simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
    omega
  have hlo4 := hPre.lo4
  have hhi4 := hPre.hi4
  have hx15 : s.xmm 15 = 0 := by have h := hret; unfold RetOK at h; exact h.2.2.1
  have hdfs : s.df = false := by have h := hret; unfold RetOK at h; exact h.2.2.2
  have hacS : ∀ a n w, S0.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [hmem]; simp
  have hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4]; simp [BitVec.toNat_sub]; omega
  have hra : S0.mem.readLE (S0.regs 4).toNat 8 = 4930331 := by
    rw [hsp0, hmem, Janus.Arm64.Memory.readLE_writeLE_self]
  have hreg0 : S0.mem.regions = s.mem.regions := by rw [hmem]; simp
  have hstr : strBytes S0.mem (hdrP s dw).toNat (hdrN s dw).toNat = strBytes s.mem (hdrP s dw).toNat (hdrN s dw).toNat := by
    apply Janus.Spec.strBytes_congr
    intro i hi
    rw [hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.bytes_writeLE_outside]
  have hargs : argWords64 S0 3 = [(s.regs 4).toNat - 40, (hdrP s dw).toNat, (hdrN s dw).toNat] := by
    apply Fv256.Amd64.ScanB.argw3
    · rw [hr0]; simp [BitVec.toNat_sub]; omega
    · rw [hr3]
    · rw [hr1]
  have hM0f := Fv256.Amd64.ScanBSb.m0_frame cfg hPre hmem
  have hLsep' : LiveSep L ([((S0.regs 4).toNat - 4096, (S0.regs 4).toNat), ((S0.regs 4).toNat + 8, (S0.regs 4).toNat + 8 + 8 * 3)] ++
        [((S0.regs 4).toNat, (S0.regs 4).toNat + 8)]) := by
    intro r hr
    have := e18 r hr
    simp only [outside_append, outside_cons, outside_nil, and_true, hsp0] at this ⊢
    omega
  have hP : RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b S0 := by
    refine Fv256.Amd64.ScanB.sb_pre R L b S0 _ _ _ hargs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hLsep' ?_
    · rw [hra]; decide
    · omega
    · omega
    · omega
    · rw [hacS, hsp0]
      exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    · exact Or.inr ⟨by omega, by rw [hacS]; exact hbuf⟩
    · exact ⟨hib1, fun _ => by rw [hacS]; exact hib2⟩
    · intro _; unfold Spec.Disjoint; omega
    · simp only [outside_cons, outside_nil, and_true, hsp0]; omega
    · rw [hr14]; exact e6
    · rw [hacS, hr14]; exact e7
    · rw [hr14, hgm, hsp0]; omega
    · simp only [outside_cons, outside_nil, and_true, hsp0, hr14]; omega
    · exact hokD
    · have := hM0f
      exact RtInv.inv_frame hM0f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Outside.of_sub e9 (Nat.le_refl _) (Nat.le_refl _)) (by rw [hr14]; exact e17)
    · exact hcost
    · intro r hr
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, hsp0] at hr
      rcases hr with (rfl | rfl) | rfl <;> exact Outside.of_sub e9 (by simp only; omega) (by simp only; omega)
  refine bytes_call2 impl R b L s S0 dw dst _ hsb hrip hP hargs hsp0 hstr hreg0 hr14 hr4 hr5 hx hdf0 hfs hx15 hdfs hra
    (by rw [hacS]; exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)) ?_
  intro S3 m M0 r0 r1 hSb hM0 hrip' hr0' hr3' hr1' hr4' hr5' hr14' hx' hdf' hfs' hS3 hmreg
  exact bytes_tail impl R R2 T b L lo hi dst tw dw s S3 m M0 r0 r1 (s.regs 5).toNat 5002336 dw.toNat hdl hret hsci htw hPre hav hPg htls hrtA hSb rfl
    (hM0.trans hmem) hrip' hr0' hr3' hr1' hr4' hr5' hr14' hx' hdf' hfs' hS3 hmreg
