import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanBPre
import Fv256.Amd64.ScanBSb
import Fv256.Amd64.ScanB1

/-!
# `Scan` (amd64), `[]byte` source: the part after `slicebytetostring` returned (the call of `scanScientificFromString` and the epilogue)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd Fv256.Amd64.ScanBSb

namespace Fv256.Amd64.ScanB

set_option maxRecDepth 100000 in
/-- `SciPre` and `DataLoaded` of the `scanScientificFromString` call after the copy -/
theorem bytes_pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst dw : BitVec 64) (s S3 : State) (m M0 : Janus.Arm64.Memory) (r0 r1 : BitVec 64) (v5 vt vd : Nat)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hPre : PreBS cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s)
    (hav : s.mem.accessible avxAddr 1 false = true) (hPg : PagesB R stAddr lo hi s.mem)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone cfg R2 s.mem ∧
      Outside (s.fsBase.toNat - 8) 8 R.rt)
    (hrtA : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hSb : SbPost R stAddr b L s (hdrP s dw) (hdrN s dw) r0 r1 M0 m ((s.regs 4).toNat - 40))
    (hM0c : M0 = ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 vt).writeLE ((s.regs 4).toNat + 24) 8 vd).writeLE
      ((s.regs 4).toNat + 8) 8 dst.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930331)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8)) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = r1)
    (hr4 : S3.regs 4 = s.regs 4 - 72#64) (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0) (hdf : S3.df = false)
    (hfs : S3.fsBase = s.fsBase)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 72) 8 4930347) (hmreg : m.regions = s.mem.regions) :
    SciPre cfg avxAddr R R2 T (b - roundupsize (hdrN s dw).toNat true) (L ++ (if (hdrN s dw).toNat = 0 then [] else [(r0.toNat, r0.toNat + (hdrN s dw).toNat)]))
      lo ((s.regs 4).toNat - 40) dst r0 (hdrN s dw) S3 ∧ Extracted.program.DataLoaded S3.mem ∧
    (∀ k, k < (hdrN s dw).toNat → S3.mem.readLE (r0.toNat + k) 1 = s.mem.readLE ((hdrP s dw).toNat + k) 1) ∧
    MemFrame s.mem S3.mem (R.rt ++ [(lo, hi)]) := by
  obtain ⟨hTop, hbytes, hF⟩ := dec_call_pre cfg hPre hSb hM0c hr0 hr3 hr1 hr4 hr14 hx15 hdf hS3 (by decide)
  have hsp := (s.regs 4).isLt
  have hlo4 := hPre.lo4
  have hhi4 := hPre.hi4
  have hEnv := hPre.env
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := hEnv
  have hs4 : (S3.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  refine ⟨⟨hTop.1, hTop.2, by omega, ?_, ?_, ?_⟩, ?_, hbytes, hF⟩
  · rw [hF.accessible]; exact hav
  · obtain ⟨hp1, hp2, hp3⟩ := hPg
    obtain ⟨hSO, hSA⟩ := hSb.soa
    have hnN : r1.toNat = (hdrN s dw).toNat := by rw [hSO.1]; simp
    have tr : ∀ a l, Fv256.IndexByte.PageReadable s.mem a l → Fv256.IndexByte.PageReadable S3.mem a l := by
      intro a l h
      unfold Fv256.IndexByte.PageReadable at h ⊢
      rcases h with h | ⟨h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨h3, by rw [hF.accessible]; exact h4⟩
    by_cases hn0 : (hdrN s dw).toNat = 0
    · exact Or.inl hn0
    · have hpos : 0 < (hdrN s dw).toNat := Nat.pos_of_ne_zero hn0
      rcases hSA with h0 | ⟨h1', h2'⟩ | ⟨h1', h2', h3', h4'⟩ | ⟨h1', h2', r, hr, hr1', hr2'⟩
      · omega
      · have hb := Janus.Arm64.Memory.readLE_lt M0 (hdrP s dw).toNat 1
        simp only [Nat.reducePow, Nat.pow_one] at hb
        exact pageR_sub (tr _ _ hp3) hpos (by omega) (by omega)
      · exact pageR_sub (tr _ _ hp1) hpos (by omega) (by omega)
      · have := tr _ _ (hp2 r hr)
        exact pageR_sub this hpos (by omega) (by omega)
  · exact tls_frame2 cfg (hi3 := (s.regs 4).toNat - 40) hF hfs hr14 (by omega) hPre.eofW hPre.eofR hPre.bigW hPre.bigR htls
  · refine dl_frame' hdl (by rw [hS3]; simp [hmreg]) hF ?_
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hrtA r h
    · simp only [List.mem_singleton] at h; subst h; exact e5

set_option maxRecDepth 100000 in
/-- the call of `scanScientificFromString` on the copy and the epilogue of `Scan` (`[]byte` source) -/
theorem bytes_tail (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s S3 : State) (m M0 : Janus.Arm64.Memory) (r0 r1 : BitVec 64) (v5 vt vd : Nat)
    (hdl : Extracted.program.DataLoaded s.mem) (hret : RetOK s)
    (hsci : SciSumm (Extracted.program.link impl))
    (htw : tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65»)
    (hPre : PreBS cfg sbAddr stAddr R R2 T b L lo hi dst (hdrP s dw) (hdrN s dw) s)
    (hav : s.mem.accessible avxAddr 1 false = true) (hPg : PagesB R stAddr lo hi s.mem)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone cfg R2 s.mem ∧
      Outside (s.fsBase.toNat - 8) 8 R.rt)
    (hrtA : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hSb : SbPost R stAddr b L s (hdrP s dw) (hdrN s dw) r0 r1 M0 m ((s.regs 4).toNat - 40))
    (hv5 : v5 = (s.regs 5).toNat)
    (hM0c : M0 = ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v5).writeLE ((s.regs 4).toNat + 16) 8 vt).writeLE ((s.regs 4).toNat + 24) 8 vd).writeLE
      ((s.regs 4).toNat + 8) 8 dst.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930331)
    (hrip : S3.rip = BitVec.ofNat 64 sci)
    (hr0 : S3.regs 0 = BitVec.ofNat 64 (m.readLE ((s.regs 4).toNat + 8) 8)) (hr3 : S3.regs 3 = r0) (hr1 : S3.regs 1 = r1)
    (hr4 : S3.regs 4 = s.regs 4 - 72#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64) (hr14 : S3.regs 14 = s.regs 14) (hx15 : S3.xmm 15 = 0)
    (hdf : S3.df = false) (hfs : S3.fsBase = s.fsBase)
    (hS3 : S3.mem = m.writeLE ((s.regs 4).toNat - 72) 8 4930347) (hmreg : m.regions = s.mem.regions) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S3
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨hpre, hdl3, hbytes, hF⟩ := bytes_pre R R2 T b L lo hi dst dw s S3 m M0 r0 r1 v5 vt vd hdl hPre hav hPg htls hrtA hSb hM0c hr0 hr3 hr1
    hr4 hr14 hx15 hdf hfs hS3 hmreg
  refine ReachesRet.call_regions (hsci R R2 T _ _ lo ((s.regs 4).toNat - 40) dst r0 (hdrN s dw)) hrip ⟨hpre, hdl3⟩ ?_
  intro S' hr hq hreg
  obtain ⟨hK, hSP, hMF⟩ := hq
  obtain ⟨k1, k4, k5, k14, kx, kdf, kfs⟩ := hK
  have hsp := (s.regs 4).isLt
  have hlo4 := hPre.lo4
  have hhi4 := hPre.hi4
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -⟩ := hPre.env
  have hzw := hPre.zwin
  have hs4 : (s.regs 4 - 72#64).toNat = (s.regs 4).toNat - 72 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrip' : S'.rip = BitVec.ofNat 64 4930347 := by
    rw [k1]; simp only [retAddrOf]
    rw [hr4, hS3, hs4, Janus.Arm64.Memory.readLE_writeLE_self]
  have hr4' : S'.regs 4 = s.regs 4 - 64#64 := by rw [k4, hr4]; bv_omega
  have hr5' : S'.regs 5 = s.regs 4 - 8#64 := by rw [k5, hr5]
  have ho8 : Outside ((s.regs 4).toNat - 8) 8 (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (dst.toNat, dst.toNat + 32)]) := by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega, by omega⟩
  have ho0 : Outside (s.regs 4).toNat 8 (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (dst.toNat, dst.toNat + 32)]) := by
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), Outside.of_sub e10 (by omega) (by omega)⟩, by omega, by omega⟩
  have hmf := hSb.mf
  have hm8o : Outside ((s.regs 4).toNat - 8) 8 (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
      ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++ (if (s.regs 4).toNat - 40 = 0 then [] else [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)])) := by
    rw [if_neg (by omega)]
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), by omega, by omega⟩, by omega⟩
  have hm0o : Outside (s.regs 4).toNat 8 (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
      ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 24)] ++ (if (s.regs 4).toNat - 40 = 0 then [] else [((s.regs 4).toNat - 40, (s.regs 4).toNat - 40 + 32)])) := by
    rw [if_neg (by omega)]
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨⟨Outside.of_sub e9 (by omega) (by omega), by omega, by omega⟩, by omega⟩
  have hm8 : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hMF.readLE _ _ ho8, hS3]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hmf.readLE _ _ hm8o, hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [hv5]; exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this)
  have hm0 : S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hMF.readLE _ _ ho0, hS3]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hmf.readLE _ _ hm0o, hM0c]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hacc : ∀ a n, S'.mem.accessible a n false = s.mem.accessible a n false := by
    intro a n
    rw [hMF.accessible, hS3, Janus.Arm64.Memory.accessible_writeLE, hmf.accessible, hM0c]
    simp only [Janus.Arm64.Memory.accessible_writeLE]
  have ha8 : S'.mem.accessible ((s.regs 4).toNat - 8) 8 false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
  have ha0 : S'.mem.accessible (s.regs 4).toNat 8 false = true := by
    rw [hacc]; exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
  have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
  janus64_run [hm8, hm0, ha8, ha0]
  have hSOa := hSb.soa
  obtain ⟨hSO, hSA⟩ := hSOa
  have hnN : r1.toNat = (hdrN s dw).toNat := by rw [hSO.1]; simp
  have hib := hPre.ibuf
  have hpn48 : (hdrP s dw).toNat + (hdrN s dw).toNat ≤ 2 ^ 48 := hib.1
  have hsyM : (cfg.strconvErrSyntax, cfg.strconvErrSyntax + 16) ∈ staticRanges cfg T := by simp [staticRanges]
  have hs1 := e14 _ hsyM
  have hs2 := Mod.static cfg hPre.mod _ hsyM
  have hrd : ∀ a n, Outside a n R.rt → Outside a n [(lo, hi)] → S3.mem.readLE a n = s.mem.readLE a n :=
    fun a n h1 h2 => hF.readLE a n (by rw [outside_append]; exact ⟨h1, h2⟩)
  have heofW := hPre.eofW
  have hbigW := hPre.bigW
  simp only [outside_cons, outside_nil, and_true] at heofW hbigW hs1
  have hpost3 := Fv256.Amd64.ScanBPre.strpost_transport cfg (R := R) (b := b) (L := L) (lo := lo) (hi := hi) (hpw := by omega) (hp0w := by omega) hbytes
    (fun r hr => List.mem_append_left _ hr)
    (hrd _ _ (Outside.of_sub hPre.eofR (Nat.le_refl _) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega))
    (hrd _ _ (Outside.of_sub hPre.eofR (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega))
    (hrd _ _ (Outside.of_sub hPre.bigR (Nat.le_refl _) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega))
    (hrd _ _ (Outside.of_sub hPre.bigR (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega))
    (hrd _ _ (Outside.of_sub hs2 (Nat.le_refl _) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega))
    (hrd _ _ (Outside.of_sub hs2 (by omega) (by omega)) (by simp only [outside_cons, outside_nil, and_true]; omega)) hSP
  have hMFall : MemFrame s.mem S'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := by
    have hF' : MemFrame s.mem S3.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := hF.mono (fun a k h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨h.1.1, h.2.1⟩)
    refine hF'.trans hMF (rs'' := R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, ?_⟩)
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, by omega, h3⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr (Or.inr (Or.inl ⟨htw, hpost3, hMFall⟩))⟩
  · simp [retAddrOf, hm0]
  · simp [setRegF_apply]
  · simp [setRegF_apply, hm8]
  · simp [setRegF_apply]; rw [k14, hr14]
  · simpa [hret.2.2.1] using kx.trans hx15
  · simp [hret.2.2.2]
  · show S'.fsBase = s.fsBase
    rw [kfs, hfs]
