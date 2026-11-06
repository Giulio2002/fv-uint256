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
# `(*uint256.Int).MarshalText() ([]byte, error)` (arm64): the decimal digits of `z`, error nil

As the amd64 theorem (`Fv256.Amd64.MarshalText`): `[]byte(z.Dec())`, `nil`, under the `slicebytetostring` and `stringtoslicebyte`
contracts and the readiness `H` for the second call, a hypothesis over every memory that is a frame of the entry memory and every string
`(p, l)` that `Dec` can return (`DecAt`, bytes `decBytes z`).  The call returns `(ptr, len, cap)` (`X0, X1, X2`) with `len ≤ cap`,
`[ptr, ptr+cap)` writable and holding the digits in its first `len` bytes and zero after, the error `(X3, X4) = (0, 0)`, and changes no byte
outside the runtime ranges and the frame.  Runtime-placement assumption: the runtime ranges lie above the first 32 bytes.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec

namespace Fv256.Arm64.MarshalText

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

theorem roundupsize_pos_small : ∀ n, n < 79 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s (688 + 48) ∧ StackOK s 4656 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4656) (4656 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4656 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 48 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 48 - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 48 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 48 - 384 - 96) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt rt 989280 1002589 960826 p l →
          H [0, p, l] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt M)))
      (fun s s' => BytesHold s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat (decBytes (val256 s.mem z.toNat)) ∧
        s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4656, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hst, hd, hout, hrt1, hrt2, hrt32, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hH2⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4656, hsp2, hwa⟩ := hst
  simp only [val256, Fv256.Util.readLE_32] at hH hH1 hH2 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [752392] calls [dec_summary_ext impl rt H z hc]
  trace_state
  sorry

end Fv256.Arm64.MarshalText
