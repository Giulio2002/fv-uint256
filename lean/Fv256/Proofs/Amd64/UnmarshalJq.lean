import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Amd64.SfdTopSpec
import Fv256.Proofs.Amd64.SfdEnvC
import Fv256.Proofs.Amd64.FromDecimalSpec
import Fv256.Proofs.Amd64.UnmarshalSpec
import Fv256.Proofs.Common.DecCongr
import Fv256.Proofs.Amd64.UnmarshalDec
import Fv256.Proofs.Amd64.UnmarshalHex
import Fv256.Proofs.Amd64.UnmarshalDecJ
import Fv256.Proofs.Amd64.FromHexLib

import Fv256.Proofs.Amd64.UnmarshalJSON0
import Fv256.Proofs.Amd64.UnmarshalQ
import Fv256.Proofs.Amd64.UnmarshalTextS

open Fv256.Amd64.UnmarshalQ
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDecJ Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalJSON

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem ju_q (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => ((PreU0m cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ HexEnv R lo hi z s) ∧ QPre cfg sbAddr R b lo pI nI s) ∧ ¬ (nI.toNat : Int) < 2 ∧ s.mem.readLE pI.toNat 1 = 34 ∧ (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (s.mem.readLE (nI.toNat + pI.toNat - 1) 1)))) - 34#8 = 0#8))
      (fun s s' =>
        (Quoted s.mem pI.toNat nI.toNat →
          (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
              s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
            (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
              s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
          (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
            (∀ v, decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
            s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .eof →
            (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0) ∧
          (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .range →
            (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
          (∀ lo' len', decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .syntax lo' len' →
            s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab))) ∧
        (¬ Quoted s.mem pI.toNat nI.toNat →
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
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨⟨⟨hpreU0, henv⟩, hQ⟩, hc1, hc2, hc3⟩ := hpre
  have hpreU := PreUm.of0 cfg (PreU0m.retOK cfg hpreU0 h_x15 h_df (by rw [h_ret]; exact hret.user)) hpreU0
  have hEnv := hpreU.toS.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hlo4 := hpreU.toS.lo4
  have hhi4 := hpreU.toS.hi4
  obtain ⟨hib1, hib2⟩ := hpreU.toS.ibuf
  have hiw := hpreU.toS.iwin
  have hr3 := hpreU.toS.r3
  have hr1 := hpreU.toS.r1
  have hr0 := hpreU.toS.r0
  have hQ' := hQ
  have hn2 : 2 ≤ nI.toNat := by omega
  have hzw := hpreU.toS.zwin
  janus64_run until [Extracted.entry + 0x2d, Extracted.entry + 0x4d] calls [hsb]
  · janus64_run until [4922944] calls [hsb]
    refine Reaches.call (Summary.withExit (UnmarshalTextS.ut_sum impl R R2 T b L lo ((s.regs 4).toNat - 56) z (pI + 1#64) (nI - 2#64) cI hif hnew hmg hmv
      hwb1 hwb2 hsb hhex hsfd) hret) ?_ ?_ ?_
    · first | rfl | decide
    · refine call_pre cfg hpreU hQ' hn2 henv ?hr0 ?hr3 ?hr1 ?hp ?hn ?hr4 ?hr14 ?hx15 ?hdf ?hret ?hF rfl
      case hr0 => simp [setRegF_apply, hr0]
      case hr3 => simp [setRegF_apply]
      case hr1 => simp [setRegF_apply]
      case hp => simp [BitVec.toNat_add]; omega
      case hn => simp [BitVec.toNat_sub]; omega
      case hr4 => simp [setRegF_apply]
      case hr14 => simp [setRegF_apply, callRegs64_apply]
      case hx15 => simpa using h_x15
      case hdf => simpa using h_df
      case hret => simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_self]; decide
      case hF =>
        repeat apply MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
        exact MemFrame.refl _ _
    · intro s' hr hq
      obtain ⟨hKept, hpost⟩ := hq
      obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := hKept
      obtain ⟨hs_ret', hs_rbp', hU⟩ := json_post cfg hpreU hn2 henv
        (by simp [BitVec.toNat_add]; omega) (by simp [BitVec.toNat_sub]; omega)
        (by
          repeat apply MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)
          exact MemFrame.refl _ _)
        rfl hpost
        (by simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint])
        (by simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
            exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; simpa using this))
      have hs_ret : s'.mem.readLE (s.regs 4).toNat 8 = ret := by rw [hs_ret']; exact h_ret
      have hs_rbp : s'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := hs_rbp'
      have hFt := hU.2.2
      janus64_run [hs_ret, hs_rbp]
      refine ⟨fun _ => ⟨fun hx => ⟨fun v h => ?_, fun e h => ?_⟩, fun hx => ⟨fun v h => ?_, (hU.2.1 hx).2.1, (hU.2.1 hx).2.2.1, (hU.2.1 hx).2.2.2⟩⟩,
        fun hnq => absurd (q_of hc1 hc2 hc3) hnq, hU.2.2⟩
      · obtain ⟨c0, c3, c4⟩ := ((hU.1 hx).1) v h
        exact ⟨by simp [c0], by simp [c3], c4⟩
      · obtain ⟨c0, c3⟩ := ((hU.1 hx).2) e h
        first | exact ⟨c0, c3⟩ | exact ⟨by simpa using c0, by simpa using c3⟩
      · obtain ⟨c0, c3, c4⟩ := ((hU.2.1 hx).1) v h
        exact ⟨by simp [c0], by simp [c3], c4⟩
  · first | exact absurd hc3 (by janus_assumption) | exact absurd hc2 (by janus_assumption) | exact absurd hc1 (by janus_assumption)

end Fv256.Amd64.UnmarshalJSON
