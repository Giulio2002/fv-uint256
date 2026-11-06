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

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec

namespace Fv256.Amd64.UnmarshalText

/-- the `SfdCfg` of this binary -/
def cfg : SfdCfg where
  ioEOF := Extracted.dataAddr.«io.EOF»
  errBig := Extracted.dataAddr.«github.com/holiman/uint256.ErrBig256Range»
  mulTab := Extracted.dataAddr.«github.com/holiman/uint256.multipliers»
  numErrType := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
  numErrItab := Extracted.dataAddr.«go:itab.*strconv.NumError,error»
  errItab := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
  synConst := Extracted.dataAddr.«.rodata#9967e7a3»
  strconvErrSyntax := Extracted.dataAddr.«strconv.ErrSyntax»
  wbFlag := Extracted.dataAddr.«runtime.writeBarrier»
  fnStr := Extracted.dataAddr.«.rodata#3d2a826c»
  mallocgc := Extracted.program.contractAddr "runtime.mallocgc"
  memmove := Extracted.program.contractAddr "runtime.memmove"
  newobject := Extracted.program.contractAddr "runtime.newobject"
  wb1 := Extracted.program.contractAddr "runtime.gcWriteBarrier1"
  wb2 := Extracted.program.contractAddr "runtime.gcWriteBarrier2"
  maxStr := Extracted.dataAddr.«.rodata#575028b4»

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

abbrev sbAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.dataAddr.«runtime.staticuint64s»

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem scratch (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI : BitVec 64)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, 0]
      (fun s => PreU cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ Extracted.program.DataLoaded s.mem)
      (fun s s' => True) := by
  intro ret hret s hs hpre
  janus64_intro hs
  obtain ⟨hpreU, hdl⟩ := hpre
  have hEnv := hpreU.env
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv
  have hlo4 := hpreU.lo4
  have hhi4 := hpreU.hi4
  janus64_data hdl [e5]
  have hbD : (s.regs 4).toNat - 40 = 0 ∨ ((s.regs 4).toNat - 40 ≤ 281474976710624 ∧
      s.mem.accessible ((s.regs 4).toNat - 40) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  have hbH : (s.regs 4).toNat - 72 = 0 ∨ ((s.regs 4).toNat - 72 ≤ 281474976710624 ∧
      s.mem.accessible ((s.regs 4).toNat - 72) 32 true = true) :=
    Or.inr ⟨by omega, Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inr rfl) (by omega) (by omega)⟩
  obtain ⟨hib1, hib2⟩ := hpreU.ibuf
  have hiw := hpreU.iwin
  have hokD := hpreU.okD
  have hokH := hpreU.okH
  have hcost := hpreU.cost
  have hr3 := hpreU.r3
  have hr1 := hpreU.r1
  have hr0 := hpreU.r0
  have hdA : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 40 ∨ (s.regs 4).toNat - 40 + 32 ≤ pI.toNat := by omega
  have hdH : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 72 ∨ (s.regs 4).toNat - 72 + 32 ≤ pI.toNat := by omega
  have hdS1 : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 104 - 4096 ∨ (s.regs 4).toNat - 104 ≤ pI.toNat := by omega
  have hdS2 : pI.toNat + nI.toNat ≤ (s.regs 4).toNat - 104 + 8 ∨ (s.regs 4).toNat - 104 + 8 + 24 ≤ pI.toNat := by omega
  janus64_run until [Extracted.entry + 0x36] calls [hsb]
  trace_state
  all_goals sorry

end Fv256.Amd64.UnmarshalText
