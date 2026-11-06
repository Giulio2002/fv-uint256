import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.Amd64.DecExt
import Fv256.GrabTac
import Fv256.ToyRuntime64
import Fv256.LinkEq

/-!
# `(*uint256.Int).MarshalJSON() ([]byte, error)` (amd64): `"` digits `"`, error nil

**Guarantee.** Go doc: "MarshalJSON marshals using the 'decimal string' representation": `[]byte("\"" + z.Dec() + "\"")`, `nil`.
The code calls `Dec` and then `runtime.concatbyte3(nil, "\"", s, "\"")`.  Under the contracts of `slicebytetostring` and `concatbyte3` and
the readiness `H` for the second call (over every memory that is a frame of the entry memory and every string `(p, l)` that `Dec` can
return), the call returns `(ptr, len, cap)`: `len ≤ cap`, `[ptr, ptr+cap)` writable and holding `marshalJSONBytes z` in its first `len`
bytes and zero after (`BytesHold`), the error `(RDI, RSI) = (0, 0)` (nil), and no byte outside the runtime ranges and the frame changes.
The quote string is the program's read-only datum at `5181392` (`"`); its bytes are unchanged by the runtime (`Outside 5181392 32 rt`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec

namespace Fv256.Amd64.MarshalJSON

abbrev cbAddr : Nat := Extracted.program.contractAddr "runtime.concatbyte3"

theorem roundupsize_pos_small : ∀ n, n < 82 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract64 (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s (0x378 + 72) ∧ StackWritable s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4640) (4640 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        Outside 5181392 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 72 - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 72 - 384 - 0x58) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
          DecAt rt 5163273 5176582 5134938 p l →
          H [0, 5181392, 1, p, l, 5181392, 1] (s.regs 14).toNat ((s.regs 4).toNat - 72) (rtView rt M)))
      (fun s s' => BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (marshalJSONBytes (s.mem.readLE z.toNat 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hout, hrt1, hrt2, hrt3, hrt32, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1, hH2⟩
  janus64_intro hs
  have hdE : decE = 4931168 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run [hdE] until [4928749] calls [dec_summary_ext impl rt H z hc]
  trace_state
  sorry

end Fv256.Amd64.MarshalJSON
