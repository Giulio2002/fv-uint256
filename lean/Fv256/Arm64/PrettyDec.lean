import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.PdCells
import Fv256.Arm64.Pd.Lift

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

namespace Fv256.Arm64.PrettyDec

/-- the address of `runtime.slicebytetostring` in the extracted program -/
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem hLib : Fv256.Arm64.LinkEq.LibIn Fv256.Arm64.PrettyProg.program Extracted.program :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem pdE_entry : Fv256.Arm64.Pd.pdE = Extracted.entry := by unfold Fv256.Arm64.Pd.pdE; decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- `PrettyDec(separator)` returns the decimal digits of `*z` with `separator` between every three digits counted from
the right (`1234567` becomes `1,234,567` for `','`), and `"0"` for zero.  The result is the string at `(X0, X1)`. -/
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, sep]
      (fun s => GuardOK s 704 ∧ StackOK s 4608 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 24) rt ∧ Ptr32 s.mem z false ∧
        (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
        (val256 s.mem z.toNat ≠ 0 →
          H [0, s.sp.toNat - 168 - plen (val256 s.mem z.toNat), plen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (prettyBytes (sep.toNat % 256) (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])) := by
  rw [← pdE_entry]
  refine Fv256.Arm64.Pd.ensures_of_summary' (Fv256.Arm64.Pd.pd_summary_E _ hLib rfl impl rt H z sep hc) ?_ ?_
  · intro ret s hret hs ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hl : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
    have hrl : (s.regs 30).toNat = ret := by
      rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
    exact ⟨hs.args 0 (by simp), hs.args 1 (by simp), h1, h2, h3, h4, h5, h6, h7, h8, by rw [hrl]; exact hret.user,
      by rw [hrl]; exact hret.aligned⟩
  · intro ret s s' hret hs hp hq
    exact ⟨⟨hq.2.1, hq.2.2.2.1, hq.2.2.1, hq.2.2.2.2.1⟩, hq.1, hq.2.2.2.2.2⟩

end Fv256.Arm64.PrettyDec
