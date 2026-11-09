import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanA4
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
/-- `scanScientificFromString`, an `'e'` at index `i`: the call `SetFromDecimal(dst, s[:i])` -/
theorem sci_some (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (s S : State) (hpc : S.rip = BitVec.ofNat 64 (sci + 0x53))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0) (hdl : Extracted.program.DataLoaded s.mem)
    (hK : Fv256.Amd64.ScanIbsCall.PostK s S lo hi dst p n)
    (hidx : Fv256.IndexByte.indexOfNat (Fv256.IndexByte.bytesOf s.mem p.toNat) n.toNat 101 ≠ 2 ^ 64 - 1) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  have hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s := ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hn64 : n.toNat < 2 ^ 64 - 1 := by have := hpw; omega
  obtain ⟨i, hsome, hi1, hilt⟩ := Fv256.Amd64.ScanIdx.indexOf_some (Fv256.IndexByte.bytesOf s.mem p.toNat) n.toNat hn64 hidx
  have hsome' : idxE (bytesAt s.mem p.toNat) n.toNat = some i := hsome
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hwin : s.mem.accessible lo (hi - lo) true = true := hEnv.2.2.2.2.1
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have e2 : (s.regs 4).toNat + 8 ≤ hi := hEnv.2.1
  have e4 : (s.regs 4).toNat % 8 = 0 := hEnv.2.2.2.1
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have hT0 : Hid (TopPre0 cfg R R2 T b L lo hi dst p n s) := hT
  have hEnv0 : Hid (Env cfg R R2 T b L lo hi s) := hEnv
  have hret00 : Hid (RetOK s) := hret0
  have hpre0 : Hid (SciPre cfg avxAddr R R2 T b L lo hi dst p n s) := hpre
  clear hT hEnv hret0 hpre
  obtain ⟨k4, k5, kfs, kdf, kmf, kidx, kdst, kp, kn, kret, krbp, kreg⟩ := hK
  have hsp := (s.regs 4).isLt
  rw [hi1] at kidx
  have hi64 : i < 2 ^ 64 - 1 := by omega
  janus64_run [kidx, kdst, kp, kn] until [sci + 0x57]
  have hfsb : 8 ≤ S.fsBase.toNat ∧ S.fsBase.toNat ≤ 2 ^ 48 := by rw [kfs]; exact htls.base
  have hfsa : (S.fsBase + 18446744073709551608#64).toNat = S.fsBase.toNat - 8 := by
    have := hfsb.1; have h2 := S.fsBase.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (S.fsBase.toNat - 8) 8 false = true := by rw [kfs, kmf.accessible]; exact htls.readable
  have hval : S.mem.readLE (S.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by rw [kfs, kmf.readLE _ _ hout]; exact htls.g
  janus64_run [hfsa, hfsb.1, hacc, hval, kidx, kdst, kp, kn] until [sfdEntry]
  have hT : TopPre0 cfg R R2 T b L lo hi dst p n s := hT0
  have hEnv : Env cfg R R2 T b L lo hi s := hEnv0
  have hret0 : RetOK s := hret00
  have hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s := hpre0
  have hinit := hpre.2.2.2.2.2.2.2
  have hF1 : MemFrame s.mem ((S.mem.writeLE ((s.regs 4).toNat - 80) 8 i).writeLE ((s.regs 4).toNat - 120) 8 4930693) [(lo, hi)] :=
    (kmf.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF2 : MemFrame s.mem ((S.mem.writeLE ((s.regs 4).toNat - 80) 8 i).writeLE ((s.regs 4).toNat - 120) 8 4930693) [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hF1.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  have hni : (BitVec.ofNat 64 i).toNat = i := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ReachesRet.call_regions (hsfd b L lo ((s.regs 4).toNat - 88) dst p (BitVec.ofNat 64 i)) rfl ?_ (fun S' hr hq hregs => ?_)
  · exact call_pre1 cfg hret0 hT hlo hF1 (ScanSfd.ra_lt _ _ _ (by omega)) (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setXmmF_apply]) hret0.2.2.2 (by rw [hni]; omega)
  · obtain ⟨k1, k2, k3, k4', k5', k6, k7⟩ := hq.1
    rcases topPost_split cfg hq with ⟨v, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hnok, hq2⟩
    · have hkeep := top_keep cfg hT (hpost := hq) (by omega)
      have hS4 : S'.regs 4 = s.regs 4 - 112#64 := by
        rw [k2]; simp [setRegF_apply]; bv_omega
      have hc0 : (S'.regs 0).toNat = 0 := by rw [c0]; rfl
      janus64_run [hc0] until [sci + 0xae]
      have hMF4 : MemFrame s.mem S'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
        hF2.trans cMF (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, by
          simp only [outside_cons, outside_nil, and_true] at h ⊢; omega⟩)
      have hbytes := str_same cfg hT hF2
      have hv0 := hv
      rw [hni] at hv0
      have hv' : decParse (bytesAt s.mem p.toNat) i = Res.ok v :=
        (Fv256.I.decParse_congr _ _ i (fun k hk => (hbytes k (by omega)))).symm.trans hv0
      have hdlS : Extracted.program.DataLoaded S'.mem := by
        refine dl_frame hdl ?_ hMF4 ?_ ?_
        · rw [hregs]; simp only [Janus.Arm64.Memory.regions_writeLE]; rw [kreg]
        · intro r hr
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl <;> simp <;> omega
        · intro r hr
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
          rcases hr with rfl | rfl
          · exact hwin
          · simpa using hT.zacc
      refine sci_after1 impl R R2 T b L lo hi dst p n i v s _ rfl hsfd hexp hmo hpre hn ?_
      simp only [Kept, retAddrOf, setRegF_apply, setXmmF_apply] at k2 k3 k4' k5' k6 k7
      refine ⟨hS4, ?_, k4', ?_, rfl, ?_, hMF4, cEnv, ?_, ?_, ?_, ?_, ?_, ?_, hsome', hilt, hv', cval, hdlS⟩
      · show S'.regs 5 = s.regs 4 - 8#64
        rw [k3]; exact k5
      · show S'.xmm 15 = 0
        exact k5'
      · show S'.fsBase = s.fsBase
        rw [k7, kfs]
      · show S'.mem.readLE ((s.regs 4).toNat - 80) 8 = i
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by omega)
      · show S'.mem.readLE ((s.regs 4).toNat + 8) 8 = dst.toNat
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact kdst
      · show S'.mem.readLE ((s.regs 4).toNat + 16) 8 = p.toNat
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact kp
      · show S'.mem.readLE ((s.regs 4).toNat + 24) 8 = n.toNat
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact kn
      · show S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact kret
      · show S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact krbp
    · have hnz := nz_of_nonok cfg hT hinit hF2 hq2 hnok (by decide)
      have hkeep := top_keep cfg hT hq2 (by omega)
      have hrbp : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact krbp
      have hret : S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        rw [hkeep _ _ (by omega) (by omega)]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        exact kret
      have hS4 : S'.regs 4 = s.regs 4 - 112#64 := by
        rw [k2]; simp [setRegF_apply]; bv_omega
      have hacc2 : S'.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
        rw [top_acc cfg hq2, hF1.accessible]
        exact Janus.Arm64.Memory.accessible_sub s.mem hEnv.2.2.2.2.1 (Or.inl rfl) (by omega) (by omega)
      have hnz' : ¬ (S'.regs 0).toNat = 0 := hnz
      janus64_run [hrbp, hret, hS4, hnz']
      have hbytes := str_same cfg hT hF2
      have hres : ∀ M : Janus.Arm64.Memory, (∀ k, k < n.toNat → bytesAt M p.toNat k = bytesAt s.mem p.toNat k) →
          (∀ v, decParse (bytesAt M p.toNat) (BitVec.ofNat 64 i).toNat ≠ .ok v) →
          sciParse (bytesAt s.mem p.toNat) n.toNat = decParse (bytesAt M p.toNat) (BitVec.ofNat 64 i).toNat := by
        intro M hM hnM
        rw [hni] at hnM ⊢
        have hc : decParse (bytesAt s.mem p.toNat) i = decParse (bytesAt M p.toNat) i :=
          Fv256.I.decParse_congr _ _ _ (fun k hk => (hM k (by omega)).symm)
        rw [Fv256.Amd64.ScanIdx.sciParse_some_nonok _ _ _ hn hsome' (fun v hv => hnM v (by rw [← hc]; exact hv)), hc]
      have hr := hres _ hbytes hnok
      unfold SciPost
      refine ⟨?_, scanStr_top cfg (off := 0) hT (by omega) hF2 (Or.inl rfl) hq2 rfl (by simp [setRegF_apply]) (by simp [setRegF_apply])
        (by omega) (by rw [hni]; omega) (fun v hv _ => absurd hv (hnok v)) (fun h => hr.trans h) (fun h => hr.trans h)
        (fun l m h => by rw [Nat.zero_add]; exact hr.trans h)⟩
      simp [Kept, retAddrOf, setRegF_apply, setXmmF_apply] at k2 k3 k4' k5' k6 k7 ⊢
      exact ⟨k4', by rw [k5', hx15]; rfl, by rw [k7, kfs]⟩

end Fv256.Amd64.ScanA
