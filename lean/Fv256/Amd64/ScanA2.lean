import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanIbsCall
import Fv256.Amd64.ScanSfd
import Fv256.Amd64.ScanIdx
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
theorem sci_none (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (s S : State) (hpc : S.rip = BitVec.ofNat 64 (sci + 0x53))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hK : Fv256.Amd64.ScanIbsCall.PostK s S lo hi dst p n)
    (hidx : Fv256.IndexByte.indexOfNat (Fv256.IndexByte.bytesOf s.mem p.toNat) n.toNat 101 = 2 ^ 64 - 1) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout⟩ := hpre
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
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
  clear hT hEnv hret0
  obtain ⟨k4, k5, kfs, kdf, kmf, kidx, kdst, kp, kn, kret, krbp⟩ := hK
  have hsp := (s.regs 4).isLt
  rw [hidx] at kidx
  janus64_run [kidx, kdst, kp, kn] until [sci + 0x57]
  have hfsb : 8 ≤ S.fsBase.toNat ∧ S.fsBase.toNat ≤ 2 ^ 48 := by rw [kfs]; exact htls.base
  have hfsa : (S.fsBase + 18446744073709551608#64).toNat = S.fsBase.toNat - 8 := by
    have := hfsb.1; have h2 := S.fsBase.isLt
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hacc : S.mem.accessible (S.fsBase.toNat - 8) 8 false = true := by rw [kmf.accessible, kfs]; exact htls.readable
  have hval : S.mem.readLE (S.fsBase.toNat - 8) 8 = (s.regs 14).toNat := by rw [kfs, kmf.readLE _ _ hout]; exact htls.g
  janus64_run [hfsa, hfsb.1, hacc, hval, kidx, kdst, kp, kn] until [sfdEntry]
  have hT : TopPre0 cfg R R2 T b L lo hi dst p n s := hT0
  have hEnv : Env cfg R R2 T b L lo hi s := hEnv0
  have hret0 : RetOK s := hret00
  have hsp := (s.regs 4).isLt
  have hF1 : MemFrame s.mem (S.mem.writeLE ((s.regs 4).toNat - 120) 8 4931000) [(lo, hi)] :=
    kmf.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF1 : MemFrame s.mem (S.mem.writeLE ((s.regs 4).toNat - 120) 8 4931000) [(lo, hi)] :=
    kmf.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF2 : MemFrame s.mem (S.mem.writeLE ((s.regs 4).toNat - 120) 8 4931000) [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hF1.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  refine ReachesRet.call (hsfd b L lo ((s.regs 4).toNat - 88) dst p n) rfl ?_ (fun S' hr hq => ?_)
  · exact call_pre1 cfg hret0 hT hlo kmf (by omega) rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setXmmF_apply]) hret0.2.2.2 (Nat.le_refl _)
  · obtain ⟨k1, k2, k3, k4, k5', k6, k7⟩ := hq.1
    have hq2 := hq
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
    janus64_run [hrbp, hret, hS4]
    have hn64 : n.toNat < 2 ^ 64 - 1 := by have := hpw; omega
    have hnone : idxE (bytesAt s.mem p.toNat) n.toNat = none := Fv256.Amd64.ScanIdx.indexOf_none (Fv256.IndexByte.bytesOf s.mem p.toNat) n.toNat hn64 hidx
    have hbytes := str_same cfg hT hF2
    have hres : ∀ M : Janus.Arm64.Memory, (∀ k, k < n.toNat → bytesAt M p.toNat k = bytesAt s.mem p.toNat k) →
        sciParse (bytesAt s.mem p.toNat) n.toNat = decParse (bytesAt M p.toNat) n.toNat := by
      intro M hM
      rw [Fv256.Amd64.ScanIdx.sciParse_none _ _ hn hnone]
      exact Fv256.I.decParse_congr _ _ _ (fun k hk => (hM k hk).symm)
    have hr := hres _ hbytes
    unfold SciPost
    refine ⟨?_, scanStr_top cfg (off := 0) hT (by omega) hF2 (Or.inl rfl) hq rfl (by simp [setRegF_apply]) (by simp [setRegF_apply])
      (by omega) (by omega) ?_ (fun h => hr.trans h) (fun h => hr.trans h) (fun l m h => by rw [Nat.zero_add]; exact hr.trans h)⟩
    · have k4' := k4
      simp [Kept, retAddrOf, setRegF_apply, setXmmF_apply] at k2 k3 k4 k5' k6 k7 ⊢
      exact ⟨k4, by rw [k5', hx15]; rfl, by rw [k7, kfs]⟩
    · intro v hv hval
      exact ⟨hr.trans hv, hval⟩
end Fv256.Amd64.ScanA
