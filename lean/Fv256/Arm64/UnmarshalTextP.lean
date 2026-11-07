import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.UnmarshalSpec

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec

namespace Fv256.Arm64.UnmarshalTextP

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
    Extracted.dataAddr.«.rodata#7233b75a»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"
abbrev fhEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).fromHex"
abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem probe (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hsb : RtLiveContract (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (fun s => PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ Extracted.program.DataLoaded s.mem ∧ (nI.toNat : Int) < 2)
      (fun s s' => True) := by
  intro ret hret s hs hpre
  janus_intro hs
  obtain ⟨hpreU, hdl, hc1⟩ := hpre
  have hEnv := hpreU.toS.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  janus_data hdl [e5]
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
  janus_run until [sfdEntry, fhEntry] calls [hsb]
  all_goals trace_state
  all_goals sorry

end Fv256.Arm64.UnmarshalTextP
