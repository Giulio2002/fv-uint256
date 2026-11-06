import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.GrabTac
import Fv256.LinkEq
import Fv256.Arm64.DecExt

/-!
# `(*uint256.Int).Value() (driver.Value, error)` (arm64): the interface value holding the string `Dec(z)`, error nil

**Guarantee.** Go doc (sql.go): "Value implements the database/sql/driver Valuer interface": the decimal string of `z` as a `driver.Value`
(an interface holding a `string`), error `nil`.  The code calls `Dec` and then `runtime.convTstring` to box the string header.  Under the
contracts of `slicebytetostring` (used by `Dec`) and the **live** `convTstring` (`RtLiveContract … convTstringSpec convTstringLive`, over
the runtime invariant `R`) and the live-set hypothesis for the second call (over every memory that is a frame of the entry memory and
every string `(p, l)` that `Dec` can return, `DecAt`: some live set `L` and budget `b` serve the request, and a string `Dec` allocated is
in `L`), the call returns `(type, data, err)`: `X0` the type descriptor of `string`, `X1` a box inside the runtime ranges holding the
header `(p, l)` of a string whose bytes are `Dec(z)`, `X2 = X3 = 0` (nil error).
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec

namespace Fv256.Arm64.Value

abbrev cvAddr : Nat := Extracted.program.contractAddr "runtime.convTstring"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (R : RtInv) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr R.rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s (688 + 32) ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt R.rt 989280 1002589 960826 p l →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
              [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l R.rt → InRanges p l L)))
      (fun s s' => s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (val256 s.mem z.toNat))) ∧
        s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hst, hd, hout, hrt1, hrt2, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hLive⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4640, hsp2, hwa⟩ := hst
  simp only [val256, Fv256.Util.readLE_32] at hH hH1 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [754556] calls [dec_summary_ext impl R.rt H z hc]
  trace_state
  sorry

end Fv256.Arm64.Value
