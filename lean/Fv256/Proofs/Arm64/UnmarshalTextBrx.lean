import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC
import Fv256.Proofs.Arm64.UnmarshalSpec
import Fv256.Proofs.Common.DecCongr
import Fv256.Proofs.Arm64.UnmarshalDec
import Fv256.Proofs.Arm64.UnmarshalHex
import Fv256.Proofs.Arm64.UnmarshalPost
import Fv256.Proofs.Arm64.FromHexLib
import Fv256.Proofs.Arm64.UnmarshalTextHead

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalDec Fv256.Arm64.UnmarshalHex Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost

namespace Fv256.Arm64.UnmarshalText

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem br_x (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) fhEntry (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => (PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s) ∧
        ¬ (nI.toNat : Int) < 2 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE pI.toNat 1))).toNat = 48 ∧ (BitVec.setWidth 32 (BitVec.ofNat 64 (s.mem.readLE (pI.toNat + 1) 1))).toNat = 120)
      (fun s s' => UTPost cfg R R2 lo hi z pI.toNat nI.toNat s s') := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨⟨hpreU, henv⟩, hc1, hc2, hc3⟩ := hpre
  have hEnv := hpreU.toS.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hlo4 := hpreU.toS.lo4
  have hhi4 := hpreU.toS.hi4
  have hbD : s.sp.toNat - 40 = 0 ∨ (s.sp.toNat - 40 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 40) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  have hbH : s.sp.toNat - 72 = 0 ∨ (s.sp.toNat - 72 ≤ 281474976710624 ∧ s.mem.accessible (s.sp.toNat - 72) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  obtain ⟨hib1, hib2⟩ := hpreU.toS.ibuf
  have hiw := hpreU.toS.iwin
  have hokD := hpreU.toS.okD
  have hokH := hpreU.toS.okH
  have hdA : pI.toNat + nI.toNat ≤ s.sp.toNat - 40 ∨ s.sp.toNat - 40 + 32 ≤ pI.toNat := by omega
  have hdH : pI.toNat + nI.toNat ≤ s.sp.toNat - 72 ∨ s.sp.toNat - 72 + 32 ≤ pI.toNat := by omega
  have hdS1 : pI.toNat + nI.toNat ≤ s.sp.toNat - 112 - 4096 ∨ s.sp.toNat - 112 - 8 ≤ pI.toNat := by omega
  have hdS2 : pI.toNat + nI.toNat ≤ s.sp.toNat - 112 + 8 ∨ s.sp.toNat - 112 + 8 + 24 ≤ pI.toNat := by omega
  janus_run until [fhEntry] calls [hsb]
  janus_grab StrAt as hSOA
  janus_grab LiveFrame as hLF
  janus_grab FreshFrom as hFr
  janus_grab 4096 as hMF
  have hP := SbPost.mk hMF hSOA hLF hFr (by janus_assumption)
  have hIsHex : IsHex s.mem pI.toNat nI.toNat := hex_of_120 hc1 hc2 hc3
  have hn2 := hIsHex.1
  have hS := hex_inst (z := z) hP hhex
  refine Reaches.call (Summary.withExit hS hret) ?_ ?_ ?_
  · first | rfl | decide
  · refine (hex_call_pre cfg hpreU henv hn2 hP rfl ?hr0 ?hr1 ?hr2 ?hsp ?hr28 ?h30a ?h30b rfl).1
    case hr0 => simp [setReg_apply, callRegs_apply]
    case hr1 => simp [setReg_apply, callRegs_apply]
    case hr2 => simp [setReg_apply, callRegs_apply]
    case hsp => simp [setReg_apply, callRegs_apply]
    case hr28 => simp [setReg_apply, callRegs_apply]
    case h30a => simp [setReg_apply, callRegs_apply]
    case h30b => simp [setReg_apply, callRegs_apply]
  · intro s' hr hq
    have hK := hq
    obtain ⟨k0, k1, k2, k3, k4, k5, -⟩ := hK
    dsimp only at k0 k1 k2 k3 k4 k5
    obtain ⟨⟨hok, herr⟩, hFr, hrd, hrb⟩ := hex_post cfg hpreU henv hn2 hP rfl
      (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) (by simp [setReg_apply, callRegs_apply]) rfl hq
    have hretlt : ret % 2 ^ 64 = ret := Nat.mod_eq_of_lt (by have := hret.user; omega)
    have hs_ra : s'.mem.readLE (s.sp.toNat - 112) 8 = ret := by rw [hrd, hretlt]
    have hs_fp : s'.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat := by
      rw [hrb]; exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; simpa using this)
    janus_run [hs_ra, hs_fp, k1]
    refine ⟨fun _ => hexPart_of (by simp [setReg_apply]) (by simp [setReg_apply]) rfl ⟨hok, herr⟩,
      fun hh => absurd hIsHex hh, hFr⟩

end Fv256.Arm64.UnmarshalText
