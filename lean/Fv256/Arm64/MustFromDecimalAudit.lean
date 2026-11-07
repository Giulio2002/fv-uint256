import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdTopSpec
import Fv256.Arm64.SfdEnvC
import Fv256.Arm64.FromDecimalSpec
import Fv256.DecCongr

/-!
# `uint256.MustFromDecimal(decimal string) *Int` (arm64)   (conditional on the `SetFromDecimal` summary `hsfd`)

`var z Int; if err := z.SetFromDecimal(decimal); err != nil { panic(err) }; return &z, nil`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.Panic Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.MustFromDecimal

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
    Extracted.dataAddr.«.rodata#7233b75a»,
    Extracted.dataAddr.«.rodata#575028b4»,
    Extracted.program.contractAddr "runtime.mallocgc",
    Extracted.program.contractAddr "runtime.memmove",
    Extracted.program.contractAddr "runtime.newobject",
    Extracted.program.contractAddr "runtime.gcWriteBarrier1",
    Extracted.program.contractAddr "runtime.gcWriteBarrier2")

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

open Fv256.C in
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Arm64.FromDecimalSpec.PreC cfg R R2 T b L lo hi Extracted.dataAddr.«type:uint256.Int#33f34945» pS nS s ∧
  Extracted.program.DataLoaded s.mem ∧ Fv256.Arm64.FromDecimalSpec.PanicInit cfg R R2 lo hi s.mem

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
open Fv256.C in
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)]))
      (fun s v _ =>
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
          v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
        (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
          InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)) := by
  sorry

end Fv256.Arm64.MustFromDecimal
