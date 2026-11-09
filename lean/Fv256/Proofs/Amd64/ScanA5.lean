import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanSfd2
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanA7
open Fv256.Amd64.ScanSfd
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanA

set_option maxRecDepth 100000 in
/-- segment 5a: exponent text `"0"` (n - i = 2 and byte 48): return nil with the mantissa -/
theorem sci_nil (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 : State) (hpc : S4.rip = BitVec.ofNat 64 (sci + 0xae))
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (h2 : n.toNat - i = 2) (hb : S4.mem.readLE (p.toNat + (i + 1)) 1 = 48)
    (hba : S4.mem.accessible (p.toNat + (i + 1)) 1 false = true) (hb' : bytesAt s.mem p.toNat (i + 1) = 48) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S4 (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have hacc : S4.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
    rw [qMF.accessible]
    exact Janus.Arm64.Memory.accessible_sub s.mem hEnv.2.2.2.2.1 (Or.inl rfl) (by omega) (by omega)
  have hwin4 : S4.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hn64 : n.toNat < 2 ^ 64 - 1 := by omega
  have hmk : (0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (i + 1) :=
    Fv256.Amd64.ScanSfd2.mask_pos _ _ (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw (by omega)).1]; omega)
      (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw (by omega)).1]; omega)
  clear hT hEnv hret0 qEnv qdl
  janus64_run [qi, qn, qp, qret, qrbp, hb, hba, q4, hmk, hwin4, hra]
  have hsc : sciParse (bytesAt s.mem p.toNat) n.toNat = Res.ok v := by
    rw [Fv256.Amd64.ScanIdx.sciParse_some_ok _ _ _ _ hn qsome qdec]
    simp only [show n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48 from ⟨by omega, hb'⟩, and_self, ite_true]
  refine ⟨?_, Or.inl ⟨v, hsc, by simp [setRegF_apply], by simp [setRegF_apply], qval⟩, ?_⟩
  · simp [Kept, retAddrOf, setRegF_apply]
    exact ⟨q14, by rw [qx, hx15], qfs⟩
  · exact qMF.mono (fun a k h => by simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢; exact h.2)


set_option maxRecDepth 100000 in
/-- segment 5b (post, exponent text parsed): the state `S'` after `SetFromDecimal(&exp, ..)` returned nil -> `Inv5` at `sci + 0x129` -/
theorem sci_post2_ok (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v e : Nat) (s S4 S3 S' : State)
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48)) (hlt : i + 1 < n.toNat)
    (hr4 : S3.regs 4 = s.regs 4 - 120#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64)
    (hr14 : S3.regs 14 = s.regs 14) (hxm : S3.xmm 15 = 0) (hdf : S3.df = s.df) (hfs : S3.fsBase = s.fsBase)
    (hmem : S3.mem = ((S4.mem.writeLE ((s.regs 4).toNat - 40) 16 0).writeLE ((s.regs 4).toNat - 24) 16 0).writeLE
      ((s.regs 4).toNat - 120) 8 4930808)
    (hF1 : MemFrame S4.mem S3.mem [(lo, hi)]) (hF2 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hz' : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40)
    (hpoff : (p + BitVec.ofNat 64 (i + 1)).toNat = p.toNat + (i + 1))
    (hn' : (n - BitVec.ofNat 64 (i + 1)).toNat = n.toNat - (i + 1))
    (hq : TopPost cfg R R2 T b L lo ((s.regs 4).toNat - 88) (s.regs 4 - 40#64) (p + BitVec.ofNat 64 (i + 1)) (n - BitVec.ofNat 64 (i + 1)) S3 S')
    (hr : S'.rip = BitVec.ofNat 64 (sci + 0x118)) (hregs : S'.mem.regions = S3.mem.regions)
    (hv : decParse (bytesAt S3.mem (p + BitVec.ofNat 64 (i + 1)).toNat) (n - BitVec.ofNat 64 (i + 1)).toNat = Res.ok e)
    (c0 : S'.regs 0 = 0) (cval : Janus.Spec.val256 S'.mem (s.regs 4 - 40#64).toNat = e)
    (cEnv : Env cfg R R2 T b L lo ((s.regs 4).toNat - 88) S')
    (cMF : MemFrame S3.mem S'.mem [(lo, (s.regs 4).toNat - 88), ((s.regs 4 - 40#64).toNat, (s.regs 4 - 40#64).toNat + 32)]) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S' (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨k1, k2, k3, k4', k5', k6, k7⟩ := hq.1
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  have hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s := ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hwin : s.mem.accessible lo (hi - lo) true = true := hEnv.2.2.2.2.1
  have hsp := (s.regs 4).isLt
  have hdo : Outside dst.toNat 32 [(lo, hi)] := by
    have := hT.zwin
    simp only [outside_cons, outside_nil, and_true]; omega
  have hkeep := Fv256.Amd64.ScanSfd2.top_keep2 cfg hT hq (by omega)
  have hS5 : S'.regs 4 = s.regs 4 - 112#64 := by
    rw [k2, hr4]; bv_omega
  have hc0 : (S'.regs 0).toNat = 0 := by rw [c0]; rfl
  have hbytes := str_same cfg hT hF2
  have hdec : decParse (fun k => bytesAt s.mem p.toNat (i + 1 + k)) (n.toNat - (i + 1)) = Res.ok e := by
    have hv2 := hv
    rw [hpoff, hn'] at hv2
    refine (Fv256.I.decParse_congr _ _ _ (fun k hk => ?_)).trans hv2
    have h1 := hbytes (i + 1 + k) (by omega)
    unfold bytesAt at h1 ⊢
    rw [show p.toNat + (i + 1) + k = p.toNat + (i + 1 + k) by omega]
    exact h1.symm
  have hMF5 : MemFrame s.mem S'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hF2.trans cMF (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, by
      simp only [outside_cons, outside_nil, and_true, hz'] at h ⊢; omega⟩)
  have hMF45 : MemFrame S4.mem S'.mem [(lo, hi)] :=
    hF1.trans cMF (rs'' := [(lo, hi)]) (fun a k h => ⟨h, by
      simp only [outside_cons, outside_nil, and_true, hz'] at h ⊢; omega⟩)
  have hwin4 : S4.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hwin
  have hdlS : Extracted.program.DataLoaded S'.mem := by
    refine dl_frame qdl ?_ hMF45 ?_ ?_
    · rw [hregs, hmem]; simp only [Janus.Arm64.Memory.regions_writeLE]
    · intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rw [hr]; simp; omega
    · intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rw [hr]; exact hwin4
  have hvd : Janus.Spec.val256 S'.mem dst.toNat = v := by
    show S'.mem.readLE dst.toNat 32 = v
    rw [hMF45.readLE _ _ hdo]; exact qval
  have hr0 : S'.rip = BitVec.ofNat 64 (sci + 0x118) := hr
  have hc0' : (S'.regs 0).toNat = 0 := hc0
  janus64_run [hc0'] until [sci + 0x129]
  refine sci_after2 impl R R2 T b L lo hi dst p n i v e s _ rfl hexp hmo hpre hn ?_
  have hslot : ∀ a k, ((s.regs 4).toNat - 112 ≤ a ∧ a + k ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 8 ≤ a) → (s.regs 4).toNat - 88 ≤ a → a + k ≤ hi →
      S'.mem.readLE a k = S4.mem.readLE a k := by
    intro a k hh h1 h2
    rw [hkeep a k h1 h2 (by omega), hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  refine ⟨hS5, ?_, ?_, ?_, ?_, ?_, hMF5, cEnv, ?_, ?_, ?_, ?_, ?_, ?_, qsome, qlt, qdec, hnn, hdec, hvd, ?_, hdlS⟩
  · show S'.regs 5 = s.regs 4 - 8#64
    rw [k3, hr5]
  · show S'.regs 14 = s.regs 14
    rw [k4', hr14]
  · show S'.xmm 15 = 0
    rw [k5', hxm]
  · rfl
  · show S'.fsBase = s.fsBase
    rw [k7, hfs]
  · show S'.mem.readLE ((s.regs 4).toNat - 80) 8 = i
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qi
  · show S'.mem.readLE ((s.regs 4).toNat + 8) 8 = dst.toNat
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qdst
  · show S'.mem.readLE ((s.regs 4).toNat + 16) 8 = p.toNat
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qp
  · show S'.mem.readLE ((s.regs 4).toNat + 24) 8 = n.toNat
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qn
  · show S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qret
  · show S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qrbp
  · rw [← hz']; exact cval


set_option maxRecDepth 100000 in
/-- segment 5b (post, exponent text rejected): the error is returned as is -/
theorem sci_post2_err (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 S3 S' : State)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48))
    (off : BitVec 64) (hoff : (off = BitVec.ofNat 64 (i + 1) ∧ i + 1 < n.toNat) ∨ (off = 0 ∧ i + 1 = n.toNat))
    (hr4 : S3.regs 4 = s.regs 4 - 120#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64)
    (hr14 : S3.regs 14 = s.regs 14) (hxm : S3.xmm 15 = 0) (hdf : S3.df = s.df) (hfs : S3.fsBase = s.fsBase)
    (hmem : S3.mem = ((S4.mem.writeLE ((s.regs 4).toNat - 40) 16 0).writeLE ((s.regs 4).toNat - 24) 16 0).writeLE
      ((s.regs 4).toNat - 120) 8 4930808)
    (hF1 : MemFrame S4.mem S3.mem [(lo, hi)]) (hF2 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)])
    (hz' : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40)
    (hpo : p.toNat ≤ (p + off).toNat ∧ (p + off).toNat + (n - BitVec.ofNat 64 (i + 1)).toNat ≤ p.toNat + n.toNat ∧
      ((off = BitVec.ofNat 64 (i + 1) ∧ i + 1 < n.toNat ∧ (p + off).toNat = p.toNat + (i + 1) ∧ (n - BitVec.ofNat 64 (i + 1)).toNat = n.toNat - (i + 1)) ∨
       (off = 0 ∧ i + 1 = n.toNat ∧ p + off = p ∧ n - BitVec.ofNat 64 (i + 1) = 0)))
    (hq : TopPost cfg R R2 T b L lo ((s.regs 4).toNat - 88) (s.regs 4 - 40#64) (p + off) (n - BitVec.ofNat 64 (i + 1)) S3 S')
    (hr : S'.rip = BitVec.ofNat 64 (sci + 0x118)) (hregs : S'.mem.regions = S3.mem.regions)
    (hnok : ∀ w, decParse (bytesAt S3.mem (p + off).toNat) (n - BitVec.ofNat 64 (i + 1)).toNat ≠ Res.ok w) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S' (SciPost cfg R R2 b L lo hi dst p n s) := by
  obtain ⟨k1, k2, k3, k4', k5', k6, k7⟩ := hq.1
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hwin : s.mem.accessible lo (hi - lo) true = true := hEnv.2.2.2.2.1
  have hsp := (s.regs 4).isLt
  have hx15 : s.xmm 15 = 0 := hret0.2.2.1
  have hkeep := Fv256.Amd64.ScanSfd2.top_keep2 cfg hT hq (by omega)
  have hnz := nz_of_nonok cfg hT hinit hF2 hq hnok (by decide)
  have hslot : ∀ a k, ((s.regs 4).toNat - 112 ≤ a ∧ a + k ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 8 ≤ a) → (s.regs 4).toNat - 88 ≤ a → a + k ≤ hi →
      S'.mem.readLE a k = S4.mem.readLE a k := by
    intro a k hh h1 h2
    rw [hkeep a k h1 h2 (by omega), hmem]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hrbp : S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qrbp
  have hret : S'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
    rw [hslot _ _ (by omega) (by omega) (by omega)]; exact qret
  have hS5 : S'.regs 4 = s.regs 4 - 112#64 := by
    rw [k2, hr4]; bv_omega
  have hacc2 : S'.mem.accessible ((s.regs 4).toNat - 8) 16 false = true := by
    rw [top_acc cfg hq, hF1.accessible, qMF.accessible]
    exact Janus.Arm64.Memory.accessible_sub s.mem hwin (Or.inl rfl) (by omega) (by omega)
  have hnz' : ¬ (S'.regs 0).toNat = 0 := hnz
  have hbytes := str_same cfg hT hF2
  have hr0 : S'.rip = BitVec.ofNat 64 (sci + 0x118) := hr
  janus64_run [hrbp, hret, hS5, hnz']
  unfold SciPost
  have hkept : ∀ F : State, F.regs 14 = S'.regs 14 → F.xmm 15 = S'.xmm 15 → F.fsBase = S'.fsBase → F.df = s.df →
      F.regs 4 = s.regs 4 + 8#64 → F.regs 5 = s.regs 5 → F.rip = retAddrOf s → Kept s F := by
    intro F a1 a2 a3 a4 a5 a6 a7
    exact ⟨a7, a5, a6, by rw [a1, k4', hr14], by rw [a2, k5', hxm, hx15], by rw [a4], by rw [a3, k7, hfs]⟩
  refine ⟨hkept _ rfl rfl rfl rfl (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [retAddrOf]), ?_⟩
  rcases hpo.2.2 with ⟨ho, hlt, hpoff, hn'⟩ | ⟨ho, heq, hpp, hn0⟩
  · have hres : ∀ M : Janus.Arm64.Memory, (∀ k, k < n.toNat → bytesAt M p.toNat k = bytesAt s.mem p.toNat k) →
        decParse (fun k => bytesAt s.mem p.toNat (i + 1 + k)) (n.toNat - (i + 1)) =
          decParse (bytesAt M (p + off).toNat) (n - BitVec.ofNat 64 (i + 1)).toNat := by
      intro M hM
      rw [hpoff, hn']
      refine Fv256.I.decParse_congr _ _ _ (fun k hk => ?_)
      have h1 := hM (i + 1 + k) (by omega)
      unfold bytesAt at h1 ⊢
      rw [show p.toNat + (i + 1) + k = p.toNat + (i + 1 + k) by omega]
      exact h1.symm
    have hr := hres _ hbytes
    exact scanStr_top cfg (off := i + 1) hT (by omega) hF2 (Or.inr ⟨by omega, by omega⟩) hq rfl (by simp [setRegF_apply])
      (by simp [setRegF_apply]) hpoff (by omega) (fun w hw _ => absurd hw (hnok w))
      (fun h => sci_tail_eof _ _ _ _ hn qsome qdec hnn (hr.trans h))
      (fun h => sci_tail_range _ _ _ _ hn qsome qdec hnn (hr.trans h))
      (fun l m h => sci_tail_syn _ _ _ _ hn qsome qdec hnn l m (hr.trans h))
  · have hn0' : (n - BitVec.ofNat 64 (i + 1)).toNat = 0 := by rw [hn0]; rfl
    have hsub0 : n.toNat - (i + 1) = 0 := by omega
    exact scanStr_top cfg (off := 0) hT (by omega) hF2 (Or.inr ⟨by omega, by omega⟩) hq rfl (by simp [setRegF_apply])
      (by simp [setRegF_apply]) (by rw [hpp]; rfl) (by rw [hn0']; omega) (fun w hw _ => absurd hw (hnok w))
      (fun _ => sci_tail_eof _ _ _ _ hn qsome qdec hnn (by rw [hsub0]; exact decParse_zero _))
      (fun h => by rw [hn0', decParse_zero] at h; simp [Res.eof, Res.range] at h)
      (fun l m h => by rw [hn0', decParse_zero] at h; simp [Res.eof, Res.syntax] at h)


set_option maxRecDepth 100000 in
/-- segment 5b: the second call `SetFromDecimal(&exp, p', n')` from the state `S3` (exp zeroed, return address pushed) and its results -/
theorem sci_call2 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 S3 : State)
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48))
    (off : BitVec 64) (hoff : (off = BitVec.ofNat 64 (i + 1) ∧ i + 1 < n.toNat) ∨ (off = 0 ∧ i + 1 = n.toNat))
    (hpc : S3.rip = BitVec.ofNat 64 sfdEntry) (hr0 : S3.regs 0 = s.regs 4 - 40#64) (hr1 : S3.regs 1 = n - BitVec.ofNat 64 (i + 1))
    (hr3 : S3.regs 3 = p + off) (hr4 : S3.regs 4 = s.regs 4 - 120#64) (hr5 : S3.regs 5 = s.regs 4 - 8#64)
    (hr14 : S3.regs 14 = s.regs 14) (hxm : S3.xmm 15 = 0) (hdf : S3.df = s.df) (hfs : S3.fsBase = s.fsBase)
    (hmem : S3.mem = ((S4.mem.writeLE ((s.regs 4).toNat - 40) 16 0).writeLE ((s.regs 4).toNat - 24) 16 0).writeLE
      ((s.regs 4).toNat - 120) 8 4930808) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S3 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4 :=
    ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hsp := (s.regs 4).isLt
  have hdf0 : s.df = false := hret0.2.2.2
  have hT0 : Hid (TopPre0 cfg R R2 T b L lo hi dst p n s) := hT
  have hEnv4 : Hid (Env cfg R R2 T b L lo ((s.regs 4).toNat - 88) S4) := qEnv
  clear hT hEnv hret0 qEnv qdl
  have hT : TopPre0 cfg R R2 T b L lo hi dst p n s := hT0
  have hF1 : MemFrame S4.mem S3.mem [(lo, hi)] := by
    rw [hmem]
    exact ((MemFrame.refl S4.mem _).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
      |>.writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hF2 : MemFrame s.mem S3.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    qMF.trans (hF1.mono (fun a k h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1))
      (rs'' := [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => ⟨h, h⟩)
  have hz' : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hpo : p.toNat ≤ (p + off).toNat ∧ (p + off).toNat + (n - BitVec.ofNat 64 (i + 1)).toNat ≤ p.toNat + n.toNat ∧
      ((off = BitVec.ofNat 64 (i + 1) ∧ i + 1 < n.toNat ∧ (p + off).toNat = p.toNat + (i + 1) ∧ (n - BitVec.ofNat 64 (i + 1)).toNat = n.toNat - (i + 1)) ∨
       (off = 0 ∧ i + 1 = n.toNat ∧ p + off = p ∧ n - BitVec.ofNat 64 (i + 1) = 0)) := by
    rcases hoff with ⟨ho, hlt⟩ | ⟨ho, heq⟩
    · obtain ⟨a1, a2⟩ := Fv256.Amd64.ScanSfd2.args_pos p n i hpw hlt
      have : (p + off).toNat = p.toNat + (i + 1) := by rw [ho]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine ⟨by omega, by omega, Or.inl ⟨ho, hlt, this, a1⟩⟩
    · obtain ⟨a1, a2⟩ := Fv256.Amd64.ScanSfd2.args_zero p n i heq
      have : p + off = p := by rw [ho]; simp
      refine ⟨by rw [this]; omega, by rw [this, a1]; simp, Or.inr ⟨ho, heq, this, a1⟩⟩
  have hret : S3.mem.readLE ((s.regs 4).toNat - 120) 8 < 2 ^ 47 := by
    rw [hmem]; exact ScanSfd.ra_lt _ _ _ (by omega)
  have hs3 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by
    rw [hr4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hEnv4' : Env cfg R R2 T b L lo ((s.regs 4).toNat - 88) S4 := hEnv4
  refine ReachesRet.call_regions (hsfd b L lo ((s.regs 4).toNat - 88) (s.regs 4 - 40#64) (p + off) (n - BitVec.ofNat 64 (i + 1))) hpc ?_
    (fun S' hr hq hregs => ?_)
  · exact Fv256.Amd64.ScanSfd2.call_pre2 cfg hT hlo hEnv4' qMF hF1 q4 q14 qx (by rw [qdf, hdf0]) hret hr4 hr0 hz' hr3 hr1 hr14 hxm
      (by rw [hdf, hdf0]) hpo.1 hpo.2.1
  · have hr' : S'.rip = BitVec.ofNat 64 (sci + 0x118) := by
      rw [hr]; unfold retAddrOf; rw [hmem, hs3, Janus.Arm64.Memory.readLE_writeLE_self]; rfl
    rcases topPost_split cfg hq with ⟨e, hv, c0, c3, cval, cEnv, cMF⟩ | ⟨hnok, hq2⟩
    · have hlt : i + 1 < n.toNat := by
        refine Classical.byContradiction (fun hge => ?_)
        rcases hpo.2.2 with ⟨_, h, _⟩ | ⟨ho, heq, hpp, hn0⟩
        · omega
        · rw [hn0] at hv
          simp [decParse_zero, Res.eof, Res.ok] at hv
      obtain ⟨ho, -, hpoff, hn'⟩ := hpo.2.2.resolve_right (fun ⟨_, h, _⟩ => by omega)
      subst ho
      exact sci_post2_ok impl R R2 T b L lo hi dst p n i v e s S4 S3 S' hexp hmo hpre0 hn hI hnn hlt hr4 hr5 hr14 hxm hdf hfs hmem hF1 hF2 hz'
        hpoff hn' hq hr' hregs hv c0 cval cEnv cMF
    · exact sci_post2_err impl R R2 T b L lo hi dst p n i v s S4 S3 S' hpre0 hn hI hnn off hoff hr4 hr5 hr14 hxm hdf hfs hmem hF1 hF2 hz'
        hpo hq2 hr' hregs hnok


set_option maxRecDepth 100000 in
theorem sci_pre2_pos (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 : State) (hpc : S4.rip = BitVec.ofNat 64 (sci + 0xae))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48))
    (h2 : n.toNat - i ≠ 2) (hlt : i + 1 < n.toNat) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S4 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  have hI0 := hI
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hwin4 : S4.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hn64 : n.toNat < 2 ^ 64 - 1 := by omega
  have hmk : (0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (i + 1) :=
    Fv256.Amd64.ScanSfd2.mask_pos _ _ (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw hlt).1]; omega)
      (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw hlt).1]; omega)
  clear hT hEnv hret0 qEnv qdl
  janus64_run [qi, qn, qp, qret, qrbp, q4, hwin4, hra, hmk, h2] until [sfdEntry]
  exact sci_call2 impl R R2 T b L lo hi dst p n i v s S4 _ hsfd hexp hmo hpre0 hn hI0 hnn (BitVec.ofNat 64 (i + 1)) (Or.inl ⟨rfl, hlt⟩) rfl rfl rfl rfl rfl q5 q14 qx rfl qfs rfl

set_option maxRecDepth 100000 in
theorem sci_pre2_end (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 : State) (hpc : S4.rip = BitVec.ofNat 64 (sci + 0xae))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48))
    (hend : i + 1 = n.toNat) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S4 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  have hI0 := hI
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hwin4 : S4.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hn64 : n.toNat < 2 ^ 64 - 1 := by omega
  have hmk : (0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) = 0 := by
    rw [(Fv256.Amd64.ScanSfd2.args_zero p n i hend).1]; exact Fv256.Amd64.ScanSfd2.mask_zero _
  have h2 : n.toNat - i ≠ 2 := by omega
  clear hT hEnv hret0 qEnv qdl
  janus64_run [qi, qn, qp, qret, qrbp, q4, hwin4, hra, hmk, h2] until [sfdEntry]
  exact sci_call2 impl R R2 T b L lo hi dst p n i v s S4 _ hsfd hexp hmo hpre0 hn hI0 hnn 0 (Or.inr ⟨rfl, hend⟩) rfl rfl rfl (by simp [setRegF_apply]) rfl q5 q14 qx rfl qfs rfl
set_option maxRecDepth 100000 in
theorem sci_pre2_b (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst p n : BitVec 64) (i v : Nat) (s S4 : State) (hpc : S4.rip = BitVec.ofNat 64 (sci + 0xae))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS')
    (hexp : ExpSumm (Extracted.program.link impl)) (hmo : ∀ z x y, MoSumm (Extracted.program.link impl) z x y)
    (hpre : SciPre cfg avxAddr R R2 T b L lo hi dst p n s) (hn : n.toNat ≠ 0)
    (hI : Inv4 cfg Extracted.program R R2 T b L lo hi dst p n i v s S4)
    (hnn : ¬ (n.toNat - (i + 1) = 1 ∧ bytesAt s.mem p.toNat (i + 1) = 48))
    (h2 : n.toNat - i = 2) (h48 : bytesAt s.mem p.toNat (i + 1) ≠ 48) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) S4 (SciPost cfg R R2 b L lo hi dst p n s) := by
  have hpre0 := hpre
  have hI0 := hI
  obtain ⟨hret0, hT, hlo, hav, hpg, htls, hout, hinit⟩ := hpre
  obtain ⟨q4, q5, q14, qx, qdf, qfs, qMF, qEnv, qi, qdst, qp, qn, qret, qrbp, qsome, qlt, qdec, qval, qdl⟩ := hI
  have hpw : p.toNat + n.toNat ≤ 2 ^ 48 := hT.pw
  have hsp := (s.regs 4).isLt
  have hlo4 : lo + 4800 ≤ (s.regs 4).toNat := hT.lo4
  have hhi : (s.regs 4).toNat + 32 ≤ hi := hT.hi32
  have hEnv : Env cfg R R2 T b L lo hi s := hT.env
  have e1 : lo ≤ (s.regs 4).toNat := hEnv.1
  have hhi48 : hi ≤ 2 ^ 48 := hEnv.2.2.1
  have hra : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47 := hret0.2.1
  have hwin4 : S4.mem.accessible lo (hi - lo) true = true := by rw [qMF.accessible]; exact hEnv.2.2.2.2.1
  have hn64 : n.toNat < 2 ^ 64 - 1 := by omega
  have hlt : i + 1 < n.toNat := by omega
  have hmk : (0#64 - (n - BitVec.ofNat 64 (i + 1))).sshiftRight 63 &&& BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (i + 1) :=
    Fv256.Amd64.ScanSfd2.mask_pos _ _ (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw hlt).1]; omega)
      (by rw [(Fv256.Amd64.ScanSfd2.args_pos p n i hpw hlt).1]; omega)
  have hpoff : (p + BitVec.ofNat 64 (i + 1)).toNat = p.toNat + (i + 1) := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hbyte : S4.mem.readLE (p.toNat + (i + 1)) 1 = bytesAt s.mem p.toNat (i + 1) := by
    unfold bytesAt
    refine qMF.readLE _ _ ?_
    simp only [outside_cons, outside_nil, and_true]
    have h1 := hT.pwin; have h2 := hT.pz
    rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> first | omega | (constructor <;> omega)
  have hbacc : S4.mem.accessible (p.toNat + (i + 1)) 1 false = true := by
    rw [qMF.accessible]
    rcases hT.pacc with h | h
    · omega
    · exact Janus.Arm64.Memory.accessible_sub s.mem h (Or.inl rfl) (by omega) (by omega)
  have hb48 : ¬ (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (bytesAt s.mem p.toNat (i + 1))))) - 48#8 = 0#8) := by
    intro h
    apply h48
    have h1 := congrArg BitVec.toNat h
    have h2 : bytesAt s.mem p.toNat (i + 1) < 256 := by
      unfold bytesAt; simpa using Janus.Arm64.Memory.readLE_lt s.mem (p.toNat + (i + 1)) 1
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat] at h1
    omega
  clear hT hEnv hret0 qEnv qdl
  janus64_run [qi, qn, qp, qret, qrbp, q4, hwin4, hra, hmk, hbyte, hbacc, hb48] until [sfdEntry]
  exact sci_call2 impl R R2 T b L lo hi dst p n i v s S4 _ hsfd hexp hmo hpre0 hn hI0 hnn (BitVec.ofNat 64 (i + 1)) (Or.inl ⟨rfl, hlt⟩) rfl rfl rfl rfl rfl q5 q14 qx rfl qfs rfl


end Fv256.Amd64.ScanA
