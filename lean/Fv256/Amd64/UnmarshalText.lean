import Extracted
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
import Fv256.Amd64.FromHexLib

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalDec Fv256.Amd64.FromHexLib

namespace Fv256.Amd64.UnmarshalText

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg :=
  (Extracted.dataAddr.«io.EOF»,
    Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»,
    Extracted.dataAddr.«github.com/holiman/uint256.multipliers»,
    Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»,
    Extracted.dataAddr.«go:itab.*strconv.NumError,error»,
    Extracted.dataAddr.«go:itab.internal/strconv.Error,error»,
    Extracted.dataAddr.«.rodata#9967e7a3»,
    Extracted.dataAddr.«strconv.ErrSyntax»,
    Extracted.dataAddr.«runtime.writeBarrier»,
    Extracted.dataAddr.«.rodata#3d2a826c»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»


/-- `input` starts with `0x` or `0X` -/
abbrev IsHex (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 48 ∧ (m.readLE (p + 1) 1 = 120 ∨ m.readLE (p + 1) 1 = 88)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (lo' hi' : Nat) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo' hi' z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' =>
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
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hpreU, hdl⟩ := hpre
  have hEnv := hpreU.toS.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hlo4 := hpreU.toS.lo4
  have hhi4 := hpreU.toS.hi4
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
  have hcostU := hpreU.toS.cost
  janus64_run until [Extracted.entry + 0x36, Extracted.entry + 0x56] calls [hsb]
  · -- decimal, input shorter than 2 bytes
    janus64_run until [Extracted.entry + 0x66] calls [hsb]
    janus_grab StrAt as hSOA
    janus_grab LiveFrame as hLF
    janus_grab FreshFrom as hFr
    janus_grab 4096 as hMF
    janus_grab roundupsize as hInv
    have hP := SbPost.mk hMF hSOA hLF hFr hInv
    have hS := sfd_inst (C := cfg) (lo := lo) (z := z) hP hsfd
    refine Reaches.call (Summary.withExit hS hret) ?pc ?pre ?post
    case pc => first | rfl | (show (4923046#64 : BitVec 64) = _; decide)
    case pre =>
      refine (dec_call_pre cfg hpreU ?hM0 hP ?hr0 ?hr3 ?hr1 ?hr4 ?hr14 ?hx15 ?hdf ?hS3 (by decide)).1
      case hM0 =>
        refine (((MemFrame.of_writeLE s.mem _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
          (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi)) (by simp) (by omega) (by omega)).writeLE _ (r := (lo, hi))
          (by simp) (by omega) (by omega)
      case hr0 => simp [setRegF_apply, callRegs64_apply]
      case hr3 => simp [setRegF_apply, callRegs64_apply]
      case hr1 => simp [setRegF_apply, callRegs64_apply]
      case hr4 => simp [setRegF_apply, callRegs64_apply]
      case hr14 => simp [setRegF_apply, callRegs64_apply]
      case hx15 => simp
      case hdf => simpa using h_df
      case hS3 => trace_state; sorry
    case post =>
      trace_state
      sorry
  all_goals sorry

end Fv256.Amd64.UnmarshalText
