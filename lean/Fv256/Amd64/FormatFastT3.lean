import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast
namespace Fv256.Amd64.FormatFast
theorem t3 (impl : List Amd64.Segment) (S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xd4)) (hb : (S.regs 0).toNat % 256 ≠ 1) (hwa : S.mem.accessible ((S.regs 4).toNat + 104) 4 false = true) (hw2 : (S.regs 4).toNat + 120 < 2^48) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xdf)) S (fun S' => True) := by
  janus64_run [hb, hwa] until [Extracted.entry + 0xd7]
  trace_state
  all_goals sorry
end Fv256.Amd64.FormatFast
