import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdTopSpec

/-!
# `uint256.FromDecimal(decimal string) (*Int, error)` (amd64)   [DRAFT: conditional on the `SetFromDecimal` summary]

`var z Int; if err := z.SetFromDecimal(decimal); err != nil { return nil, err }; return &z, nil`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec

namespace Fv256.Amd64.FromDecimal

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

abbrev sfdEntry : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).SetFromDecimal"

open Fv256.C in
/-- precondition of `FromDecimal(s)` (string pointer in `RAX`, length in `RBX`): the `SetFromDecimal` model facts, minus the receiver `z`
(which `newobject` allocates), for the stack window `[lo, hi)`; `b` is the heap budget at entry, `L` the live set -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = pS ∧ s.regs 3 = nS ∧ Mod cfg R R2 T L ∧
  Env cfg R R2 T b L lo hi s ∧ lo + 4856 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 24 ≤ hi ∧
  R.ok cfg.newobject [Extracted.dataAddr.«type:uint256.Int#33f34945»] ∧ blockSize 32 false ≤ b ∧
  (∀ z : Nat, InRanges z 32 R.rt → MultOK cfg z lo hi s.mem) ∧
  s.mem.accessible cfg.ioEOF 16 false = true ∧ Outside cfg.ioEOF 16 [(lo, hi)] ∧
  s.mem.accessible cfg.errBig 16 false = true ∧ Outside cfg.errBig 16 [(lo, hi)] ∧
  Buffer s pS nS.toNat false ∧ (pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  ChunkAll cfg R R2 L (b - blockSize 32 false) pS.toNat nS.toNat lo hi s.mem

open Fv256.C in
theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
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
    (hsfd : ∀ (b' : Nat) (L' : List (Nat × Nat)) (z pS' nS' : BitVec 64),
      SfdSummary cfg (Extracted.program.link impl) sfdEntry R R2 T b' L' lo hi z pS' nS') :
    Ensures (Extracted.program.link impl) Extracted.entry [pS, nS] (Pre R R2 T b L lo hi pS nS)
      (fun s s' =>
        (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof →
          s'.regs 0 = 0 ∧ (s'.regs 3).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.ioEOF + 8) 8) ∧
        (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range →
          s'.regs 0 = 0 ∧ (s'.regs 3).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.errBig + 8) 8) ∧
        (∀ lo' len', decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' →
          s'.regs 0 = 0 ∧ s'.regs 3 = BitVec.ofNat 64 cfg.numErrItab) ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])) := by
  intro ret hret s hs hpre
  janus64_intro hs
  sorry

end Fv256.Amd64.FromDecimal
