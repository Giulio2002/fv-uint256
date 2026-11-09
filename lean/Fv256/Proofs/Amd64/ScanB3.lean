import Extracted
import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanCfg
import Fv256.Proofs.Amd64.ScanBPre
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Common.GrabLive
import Fv256.Proofs.Amd64.ScanBData

/-!
# `Scan` (amd64), Level B segment: an unsupported dynamic type (`errors.New("unsupported type")`)
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanCfg Fv256.Amd64.ScanSfd

namespace Fv256.Amd64.ScanB

set_option maxRecDepth 100000 in
/-- the last three instructions of the unsupported-type path: `pop rbp; ret` after the stores of the error object -/
theorem other_ret (impl : List Janus.Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s F0 : State) (m : Janus.Arm64.Memory) (ptr : BitVec 64) (rr : Nat × Nat) (R2 : IfaceModel)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hretok : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) (hlo : lo + 4992 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi)
    (e3 : hi ≤ 2 ^ 48) (e5 : s.mem.accessible lo (hi - lo) true = true)
    (hrt : ∀ r ∈ R.rt, s.mem.accessible r.1 (r.2 - r.1) true = true)
    (hdo : Outside dst.toNat 32 R.rt) (hdw : dst.toNat + 32 ≤ lo ∨ hi ≤ dst.toNat)
    (htw : tw ≠ 0 ∧ tw.toNat ≠ Extracted.dataAddr.«type:string#f88732b8» ∧ tw.toNat ≠ Extracted.dataAddr.«type:[]uint8#7efbbf65»)
    (hrip : F0.rip = BitVec.ofNat 64 4930438) (hF0m : F0.mem = (m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680)
    (hF04 : F0.regs 4 = s.regs 4) (hF05 : F0.regs 5 = s.regs 5) (hF00 : F0.regs 0 = 5183688#64) (hF03 : F0.regs 3 = ptr)
    (hF014 : F0.regs 14 = s.regs 14) (hF0x : F0.xmm 15 = s.xmm 15) (hF0df : F0.df = s.df) (hF0fs : F0.fsBase = s.fsBase)
    (hrr : rr ∈ R.rt) (hr1 : rr.1 ≤ ptr.toNat) (hr2 : ptr.toNat + 16 ≤ rr.2)
    (hAp : ApartAll ptr.toNat 16 L)
    (hFF : MemFrame s.mem ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680) (R.rt ++ [(lo, hi)]))
    (hm0 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8)
    (ha0 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).accessible (s.regs 4).toNat 8 false = true) :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) F0
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  have hsp := (s.regs 4).isLt
  have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
  have hm0' : F0.mem.readLE (F0.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by rw [hF0m, hF04]; exact hm0
  have ha0' : F0.mem.accessible (F0.regs 4).toNat 8 false = true := by rw [hF0m, hF04]; exact ha0
  have ha0m : m.accessible (s.regs 4).toNat 8 false = true := by
    have := ha0; simpa [Janus.Arm64.Memory.accessible_writeLE] using this
  janus64_run [hm0', ha0', ha0m, hm0, ha0]
  have hmsg := Fv256.Amd64.ScanBData.msgB s.mem hdl
  have hdM := Fv256.Amd64.ScanBData.aprtM s.mem hdl e5
  have hitab : Extracted.dataAddr.«go:itab.*errors.errorString,error» = 5183688 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inr (Or.inr (Or.inr ⟨htw.1, htw.2.1, htw.2.2, ?_, ⟨ptr.toNat, 5142680, ?_, ⟨rr, hrr, hr1, hr2⟩, hAp, ?_, ?_, ?_⟩, ?_, hFF⟩))⟩
  · simp [retAddrOf]
  · simp [setRegF_apply]
  · simp [setRegF_apply, hF05]
  · simp [setRegF_apply, hF014]
  · simpa using hF0x
  · rfl
  · simpa using hF0fs
  · simp [setRegF_apply, hF00, hitab]
  · simp [setRegF_apply, hF03]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · intro k hk
    have ho : Outside (5142680 + k) 1 (R.rt ++ [(lo, hi)]) := by
      simp only [outside_append, outside_cons, outside_nil, and_true]
      refine ⟨outside_of_all _ (fun r hr => ?_), by omega⟩
      have := Fv256.Amd64.ScanBData.aprtM s.mem hdl (hrt r hr)
      omega
    rw [hFF.readLE _ _ ho]
    exact hmsg k hk
  · unfold Janus.Spec.val256
    refine hFF.readLE _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hdo, by omega⟩

set_option maxRecDepth 100000 in
/-- Scan with an unsupported dynamic type: allocate `errors.errorString{"unsupported type"}` -/
theorem scan_other (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 Extracted.entry) (hret : RetOK s)
    (hdl : Extracted.program.DataLoaded s.mem)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hpre : ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» avxAddr sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s)
    (htw : tw ≠ 0 ∧ tw.toNat ≠ Extracted.dataAddr.«type:string#f88732b8» ∧ tw.toNat ≠ Extracted.dataAddr.«type:[]uint8#7efbbf65») :
    ReachesRet (Extracted.program.link impl) (retAddrOf s) s
      (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s) := by
  obtain ⟨h0, h3, h1, hlo, hhi, hcase⟩ := hpre
  rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, hta, hto, hrt, hMod, hEnv, hok, hbs, hdo, hdw⟩
  · exact absurd h htw.1
  · exact absurd h htw.2.1
  · exact absurd h htw.2.2
  · have hEnv' := hEnv
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
    have hsp := (s.regs 4).isLt
    have hw1 : s.mem.accessible ((s.regs 4).toNat - 8) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hw2 : s.mem.accessible ((s.regs 4).toNat + 16) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hw3 : s.mem.accessible ((s.regs 4).toNat + 24) 8 true = true :=
      Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)
    have hsp48 : (s.regs 4).toNat + 32 < 2 ^ 64 := by omega
    have htyS : Extracted.dataAddr.«type:string#f88732b8» = 5008128 := by decide
    have htyB : Extracted.dataAddr.«type:[]uint8#7efbbf65» = 5002336 := by decide
    have hn0 : tw.toNat ≠ 0 := fun h => htw.1 (BitVec.eq_of_toNat_eq h)
    have hneS : s.regs 3 ≠ 5008128#64 := by
      intro h; apply htw.2.1; rw [h3] at h; rw [htyS, h]; rfl
    have hneB : s.regs 3 ≠ 5002336#64 := by
      intro h; apply htw.2.2; rw [h3] at h; rw [htyB, h]; rfl
    have hn0' : (s.regs 3).toNat ≠ 0 := by rw [h3]; exact hn0
    have hds := Fv256.Amd64.ScanBData.tsz _ hdl
    have hdp := Fv256.Amd64.ScanBData.tpb _ hdl
    have hda := Fv256.Amd64.ScanBData.accE _ hdl
    have hdj := Fv256.Amd64.ScanBData.aprtE s.mem hdl e5
    have htw48 : tw.toNat + 16 + 4 ≤ 2 ^ 48 := Fv256.Amd64.ScanBPre.acc_le48 (n := 4) hta
    have hh16 : tw.toNat + 16 + 4 ≤ lo ∨ hi ≤ tw.toNat + 16 := by
      have := hto; simp only [outside_cons, outside_nil, and_true] at this; exact this
    have hbs' : 16 ≤ b := Nat.le_trans (by decide) hbs
    have hF : MemFrame s.mem ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 tw.toNat).writeLE
        ((s.regs 4).toNat + 24) 8 dw.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930405) [(lo, hi)] := by
      have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
      refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)
    have hinv' : R.inv b L (s.regs 14).toNat (view R.rt L ((((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat + 16) 8 tw.toNat).writeLE
        ((s.regs 4).toNat + 24) 8 dw.toNat).writeLE ((s.regs 4).toNat - 72) 8 4930405)) :=
      RtInv.inv_frame' (ws := [(lo, hi)]) hF (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Or.inl e9) e17
    have hLsep : ∀ r ∈ L, Outside r.fst (r.snd - r.fst)
        ([((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72), ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 8)] ++
          [((s.regs 4).toNat - 72, (s.regs 4).toNat - 72 + 8)]) := by
      intro r hr
      have := e18 r hr
      simp only [outside_append, outside_cons, outside_nil, and_true] at this ⊢
      have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
      omega
    janus64_run [hinv', hLsep, e13, hbs', htw48, hn0', hneS, hneB, e7, e6, e8, hta, hds, hdp, hda] until [Extracted.entry + 0xc6] calls [hnew.pos L b]
    all_goals
      fv_live_names ptr junk f x yh m zh kr
      janus_grab 4096 as hMF
      janus_grab ApartAll as hAp
      janus_grab InRanges as hIn
      have hmsg := Fv256.Amd64.ScanBData.msgB s.mem hdl
      have hdM := Fv256.Amd64.ScanBData.aprtM s.mem hdl e5
      have hlo' : lo + 4992 ≤ (s.regs 4).toNat := hlo
      obtain ⟨rr, hrr, hr1, hr2⟩ := hIn
      have hFF : MemFrame s.mem ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680) (R.rt ++ [(lo, hi)]) := by
        have h1 : MemFrame s.mem m (R.rt ++ [(lo, hi)]) := by
          refine hF.trans hMF (rs'' := R.rt ++ [(lo, hi)]) (fun a k h => ?_)
          simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
          obtain ⟨h1, h2⟩ := h
          exact ⟨h2, h1, by omega, by omega⟩
        exact (h1.writeLE _ (r := rr) (by simp [hrr]) (by omega) (by omega)).writeLE _ (r := rr) (by simp [hrr]) (by omega) (by omega)
      have hrw := MemFrame.outside_mem e9 hrr
      have ho8 : Outside ((s.regs 4).toNat - 8) 8 (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
          ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 8)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub e9 (by omega) (by omega), by omega, by omega⟩
      have ho0 : Outside (s.regs 4).toNat 8 (R.rt ++ [((s.regs 4).toNat - 72 - 4096, (s.regs 4).toNat - 72),
          ((s.regs 4).toNat - 72 + 8, (s.regs 4).toNat - 72 + 8 + 8)]) := by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub e9 (by omega) (by omega), by omega, by omega⟩
      have hm8 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hMF.readLE _ _ ho8]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this)
      have hm0 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := by
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
        rw [hMF.readLE _ _ ho0]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      have ha8 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).accessible ((s.regs 4).toNat - 8) 8 false = true := by
        rw [hFF.accessible]
        exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
      have ha0 : ((m.writeLE (ptr.toNat + 8) 8 16).writeLE ptr.toNat 8 5142680).accessible (s.regs 4).toNat 8 false = true := by
        rw [hFF.accessible]
        exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
      exact other_ret impl R b L lo hi dst tw dw s _ m ptr rr R2 hdl hret.2.1 hlo hhi e3 e5 hrt hdo hdw htw (by rfl) (by rfl) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply, hm8]) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply]) (by rfl) (by rfl) hrr hr1 hr2 hAp hFF hm0 ha0

end Fv256.Amd64.ScanB
