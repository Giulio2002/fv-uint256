import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.UnmarshalSpec
import Fv256.Proofs.Arm64.UnmarshalSpecJ
import Fv256.Proofs.Common.DecCongr
import Fv256.Proofs.Arm64.UnmarshalDecJ
import Fv256.Proofs.Arm64.UnmarshalDecN
import Fv256.Proofs.Arm64.UnmarshalHex
import Fv256.Proofs.Arm64.UnmarshalHexN
import Fv256.Proofs.Arm64.UnmarshalPost
import Fv256.Proofs.Arm64.UnmarshalJPost
import Fv256.Proofs.Arm64.FromHexLib
import Fv256.Proofs.Arm64.UnmarshalJSONHead
import Fv256.Proofs.Arm64.UnmarshalKeepN
import Fv256.Proofs.Arm64.UnmarshalNest

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalSpecJ Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalJPost

namespace Fv256.Arm64.UnmarshalJSON

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem jq_X (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) fhEntry (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => (PreJ cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s) ∧ ¬ (nI.toNat : Int) < 2 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE pI.toNat 1))).toNat = 34 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + (nI.toNat - 1)) 1))).toNat = 34 ∧
        ¬ ((nI.toNat - 2 : Nat) : Int) < 2 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + 1) 1))).toNat = 48 ∧ ¬ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + 2) 1))).toNat = 120 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + 2) 1))).toNat = 88)
      (fun s s' => JPost cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨⟨hpreJ, henv⟩, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := hpre
  have hQ : Quoted s.mem pI.toNat nI.toNat := q_of hc1 hc2 hc3
  have hpreJc := hpreJ
  have hpreJ' := hpreJ
  obtain ⟨hpre0, -, hext⟩ := hpreJ'
  obtain ⟨hlo5, hokH, hokD, hcost, hchunk⟩ := hext hQ
  obtain ⟨⟨-, -, -, -, hEnv, hlo4, hhi4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hib1, hib2⟩, hiw, -⟩, -, -⟩ := hpreJ
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hn2 : 2 ≤ nI.toNat := hQ.1
  have hbD : s.sp.toNat - 152 = 0 ∨ (s.sp.toNat - 152 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 152) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  have hibs : s.mem.accessible (pI.toNat + 1) (nI.toNat - 2) false = true :=
    Janus.Arm64.Memory.accessible_sub s.mem hib1 (Or.inl rfl) (Nat.le_succ _) (sub_arith _ _ hn2)
  have hdA : pI.toNat + 1 + (nI.toNat - 2) ≤ s.sp.toNat - 152 ∨ s.sp.toNat - 152 + 32 ≤ pI.toNat + 1 := by omega
  have hdS1 : pI.toNat + 1 + (nI.toNat - 2) ≤ s.sp.toNat - 80 - 112 - 4096 ∨ s.sp.toNat - 80 - 112 - 8 ≤ pI.toNat + 1 := by omega
  have hdS2 : pI.toNat + 1 + (nI.toNat - 2) ≤ s.sp.toNat - 80 - 112 + 8 ∨ s.sp.toNat - 80 - 112 + 8 + 24 ≤ pI.toNat + 1 := by omega
  janus_run until [fhEntry] calls [hsb]
  janus_grab StrAt as hSOA
  janus_grab LiveFrame as hLF
  janus_grab FreshFrom as hFr
  janus_grab 4096 as hMF
  have hp' : (pI + 1#64).toNat = pI.toNat + 1 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; have := pI.isLt; omega
  have hn' : (nI - 2#64).toNat = nI.toNat - 2 := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := nI.isLt; omega
  obtain ⟨T, hT0, hT1, hT2, hTsp, hT28, hTmem⟩ := UnmarshalNest.exists_T s
    ((((s.mem.writeLE (BitVec.toNat s.sp - 80) 8 ret).writeLE (BitVec.toNat s.sp - 88) 8 (BitVec.toNat (s.regs 29))).writeLE
      (BitVec.toNat s.sp + 16) 8 pI.toNat).writeLE (BitVec.toNat s.sp + 8) 8 z.toNat) z (pI + 1#64) (nI - 2#64) (s.sp - 80#64)
  have hF : MemFrame s.mem T.mem [(lo, hi)] := by
    rw [hTmem]
    exact (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
      (by simp) (by omega) (by omega)
  have hTsp' : T.sp.toNat = s.sp.toNat - 80 := by
    rw [hTsp]; have := s.sp.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hpreT := UnmarshalSpecJ.preU_sub cfg hpreJc hQ hn2 hp' hn' hT0 hT1 hT2 hTsp hT28 hF
  have henvT := UnmarshalNest.hexEnv_frame henv hF
  have hbytesT : strBytes T.mem (pI.toNat + 1) (nI.toNat - 2) = strBytes s.mem (pI.toNat + 1) (nI.toNat - 2) := by
    exact strBytes_of_frame hF (by simp only [outside_cons, outside_nil, and_true]; omega)
  have haccT : ∀ x y, T.mem.accessible x y false = s.mem.accessible x y false := fun x y => hF.accessible x y false
  have o1 : BitVec.toNat s.sp - 192 = BitVec.toNat s.sp - 80 - 112 := by omega
  have hP := UnmarshalNest.sbpost_nest (Sj := s) (T := T) (sp := BitVec.toNat s.sp - 80) hp' hn' hT28 hbytesT o1 hMF hSOA haccT hLF hFr
    (by janus_assumption)
  have o8h : BitVec.toNat s.sp - 152 = BitVec.toNat s.sp - 80 - 72 := by omega
  rw [o8h] at hP
  have o2 : BitVec.toNat s.sp - 200 = BitVec.toNat s.sp - 80 - 120 := by omega
  have o3 : BitVec.toNat s.sp - 64 = BitVec.toNat s.sp - 80 + 16 := by omega
  have o4 : BitVec.toNat s.sp - 72 = BitVec.toNat s.sp - 80 + 8 := by omega
  have o7 : BitVec.toNat s.sp - 80 + 8 = BitVec.toNat s.sp - 72 := by omega
  have o8 : BitVec.toNat s.sp - 120 = BitVec.toNat s.sp - 80 - 40 := by omega
  have hIsHex : IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) := hex_of_88 hc4 hc5 hc7
  have hn2' : 2 ≤ (nI - 2#64).toNat := by rw [hn']; exact hIsHex.1
  have hS := UnmarshalHexN.hex_inst (z := z) hP hhex
  refine Reaches.call (Summary.withExit hS hret) ?_ ?_ ?_
  · first | rfl | decide
  · refine (UnmarshalHexN.hex_call_pre cfg hpreT hTsp' henvT hn2' hP (ra := 752680) (v29 := BitVec.toNat s.sp - 88)
      (by rw [hTmem, hp', ← o1, ← o2, ← o3, ← o4]) ?hr0 ?hr1 ?hr2 ?hsp ?hr28 ?h30a ?h30b rfl).1
    case hr0 => simp [setReg_apply, callRegs_apply, o7]
    case hr1 => simp [setReg_apply, callRegs_apply]
    case hr2 => simp [setReg_apply, callRegs_apply]
    case hsp => rw [hTsp]; simp [setReg_apply, callRegs_apply]; bv_omega
    case hr28 => simp [setReg_apply, callRegs_apply, hT28]
    case h30a => simp [setReg_apply, callRegs_apply]
    case h30b => simp [setReg_apply, callRegs_apply]
  · intro s' hr hq
    have hK := hq
    obtain ⟨k1, k2, k3, k4, k5, k6, -⟩ := hK
    dsimp only at k1 k2 k3 k4
    obtain ⟨⟨hok, herr⟩, hFr, hrd, hrb⟩ := UnmarshalHexN.hex_post cfg hpreT hTsp' henvT hn2' hP (ra := 752680)
      (v29 := BitVec.toNat s.sp - 88) (by rw [hTmem, hp', ← o1, ← o2, ← o3, ← o4])
      (by simp [setReg_apply, callRegs_apply, o7]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply])
      (by rw [hTsp]; simp [setReg_apply, callRegs_apply]; bv_omega) (by simp [setReg_apply, callRegs_apply, hT28])
      (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) rfl hq
    have hkeep := UnmarshalKeepN.hex_keep cfg hpreT hTsp' hP (ra := 752680) (v29 := BitVec.toNat s.sp - 88)
      (by rw [hTmem, hp', ← o1, ← o2, ← o3, ← o4]) (by rw [hTsp]; simp [setReg_apply, callRegs_apply]; bv_omega) rfl hq
    have hs_raU : s'.mem.readLE (BitVec.toNat s.sp - 192) 8 = 752680 := by
      rw [o1, hrd]; try exact Nat.mod_eq_of_lt (by omega)
    have hs_fpU : s'.mem.readLE (BitVec.toNat s.sp - 200) 8 = BitVec.toNat s.sp - 88 := by
      rw [o2, hrb]; exact Nat.mod_eq_of_lt (by have := s.sp.isLt; omega)
    have hretlt : ret % 2 ^ 64 = ret := Nat.mod_eq_of_lt (by have := hret.user; omega)
    have o9 : BitVec.toNat s.sp - 80 - 8 = BitVec.toNat s.sp - 88 := by omega
    have hs_raJ : s'.mem.readLE (BitVec.toNat s.sp - 80) 8 = ret := by
      rw [hkeep.1, hTmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h8, hretlt]
    have hs_fpJ : s'.mem.readLE (BitVec.toNat s.sp - 88) 8 = (s.regs 29).toNat := by
      have k2 := hkeep.2
      rw [o9] at k2
      rw [k2, hTmem]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h8]; exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
    janus_run [hs_raU, hs_fpU, hs_raJ, hs_fpJ, k1]
    have hd : HexPart z T.mem (pI + 1#64).toNat (nI - 2#64).toNat s' := ⟨hok, herr⟩
    rw [hp', hn'] at hd
    have hps := hpreT.toS
    have hev := henv.2.2.2.2.2.1
    simp only [outside_cons, outside_nil, and_true] at hev
    have hd2 := hexPart_frame hF (by omega) (by omega) hd
    refine ⟨fun _ => ⟨fun _ => hexPart_of (by simp [setReg_apply]) (by simp [setReg_apply]) rfl hd2,
      fun hh => absurd hIsHex hh⟩, fun hnq => absurd hQ hnq, ?_⟩
    refine hF.trans hFr ?_
    intro a n h
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    exact ⟨h3, ⟨h1, h2⟩, h3, h4⟩

end Fv256.Arm64.UnmarshalJSON
