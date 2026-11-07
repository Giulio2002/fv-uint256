import Extracted
import Fv256.Amd64.UnmarshalTextS0
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec
import Fv256.Amd64.SfdEnvC
import Fv256.Amd64.FromDecimalSpec
import Fv256.Amd64.UnmarshalSpec
import Fv256.DecCongr
import Fv256.Amd64.UnmarshalDec
import Fv256.Amd64.UnmarshalHex
import Fv256.Amd64.FromHexLib

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalTextS

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem br_X (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hhex : ∀ (z hp len : BitVec 64), Summary (Extracted.program.link impl) 4922368 (FromHexPre z hp len) (FromHexPost z hp len))
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Summary (Extracted.program.link impl) utEntry
      (fun s => (PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s ∧ Extracted.program.DataLoaded s.mem) ∧ ¬ (nI.toNat : Int) < 2 ∧ s.mem.readLE pI.toNat 1 = 48 ∧ ¬ (Bw s.mem pI.toNat - 120#8 = 0#8) ∧ Bw s.mem pI.toNat - 88#8 = 0#8)
      (fun s s' =>
        (IsHex s.mem pI.toNat nI.toNat →
          (∀ v, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (∀ e, parseHex (bytesAt s.mem pI.toNat) nI.toNat = .error e →
            s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
            s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
        (¬ IsHex s.mem pI.toNat nI.toNat →
          (∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])) := by
  intro s hpc hpre
  obtain ⟨⟨hpreU, henv, hdl⟩, hc1, hc2, hc3, hc4⟩ := hpre
  have hEnv := hpreU.toS.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hlo4 := hpreU.toS.lo4
  have hhi4 := hpreU.toS.hi4
  have h_x15 : s.xmm 15 = 0 := by have h := hpreU.toS.ret; unfold RetOK at h; exact h.2.2.1
  have h_df : s.df = false := by have h := hpreU.toS.ret; unfold RetOK at h; exact h.2.2.2
  have h_rip : s.rip = BitVec.ofNat 64 utEntry := hpc
  janus64_data hdl [e5]
  have hbD : (s.regs 4).toNat - 40 = 0 ∨ ((s.regs 4).toNat - 40 ≤ 281474976710624 ∧
      s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  have hbH : (s.regs 4).toNat - 72 = 0 ∨ ((s.regs 4).toNat - 72 ≤ 281474976710624 ∧
      s.mem.accessible ((s.regs 4).toNat - 72) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  obtain ⟨hib1, hib2⟩ := hpreU.toS.ibuf
  have hiw := hpreU.toS.iwin
  have hokD := hpreU.toS.okD
  have hokH := hpreU.toS.okH
  have hr3 := hpreU.toS.r3
  have hr1 := hpreU.toS.r1
  have hr0 := hpreU.toS.r0
  have hdA : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 40 + 32 ≤ pI.toNat := by omega
  have hdH : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 72 + 32 ≤ pI.toNat := by omega
  have hdS1 : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 104 - 4096 ∨ (s.regs 4).toNat - 104 ≤ pI.toNat := by omega
  have hdS2 : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 104 + 8 ∨ (s.regs 4).toNat - 104 + 8 + 24 ≤ pI.toNat := by omega
  janus64_run until [utEntry + 0x36, utEntry + 0x56] calls [hsb]
  · exact absurd (by janus_assumption) hc3
  · janus64_run until [4922368] calls [hsb]
    janus_grab StrAt as hSOA
    janus_grab LiveFrame as hLF
    janus_grab FreshFrom as hFr
    janus_grab 4096 as hMF
    have hP := SbPost.mk hMF hSOA hLF hFr (by janus_assumption)
    have hIsHex : IsHex s.mem pI.toNat nI.toNat := hex_of_88 (by janus_assumption) (by janus_assumption) (by janus_assumption)
    have hn2 := hIsHex.1
    have hS := hex_inst (z := z) hP hhex
    refine ReachesRet.call hS ?_ ?_ ?_
    · first | rfl | decide
    · refine (hex_call_pre cfg hpreU henv hn2 hP rfl ?hr0 ?hr3 ?hr1 ?hr4 ?hr14 ?hx15 ?hdf rfl ?hretv).1
      case hr0 => simp [setRegF_apply, callRegs64_apply]
      case hr3 => simp [setRegF_apply, callRegs64_apply]
      case hr1 => simp [setRegF_apply, callRegs64_apply]
      case hr4 => simp [setRegF_apply, callRegs64_apply]
      case hr14 => simp [setRegF_apply, callRegs64_apply]
      case hx15 => simp
      case hdf => simpa using h_df
      case hretv => decide
    · intro s' hr hq
      have hK := hq
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, -⟩ := hK
      obtain ⟨⟨hok, herr⟩, hFr, hrd, hrb⟩ := hex_post cfg hpreU henv hn2 hP rfl
        (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply])
        (by simp [setRegF_apply, callRegs64_apply]) (by simp [setRegF_apply, callRegs64_apply])
        (by simp [setRegF_apply, callRegs64_apply]) (by simp) (by simpa using h_df) rfl (by decide) hq
      have hs_ret : s'.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 := hrd
      have hs_rbp : s'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
        rw [hrb]; exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this)
      janus64_run [hs_ret, hs_rbp]
      refine ⟨fun _ => ⟨fun v h => ?_, fun e h => ?_⟩, fun hh => absurd hIsHex hh, hFr⟩
      · obtain ⟨c0, c3, c4⟩ := hok v h
        exact ⟨by simp [c0], by simp [c3], c4⟩
      · obtain ⟨c0, c3⟩ := herr e h
        first | exact ⟨c0, c3⟩ | exact ⟨by simpa using c0, by simpa using c3⟩
  · exact absurd hc4 (by janus_assumption)

end Fv256.Amd64.UnmarshalTextS
