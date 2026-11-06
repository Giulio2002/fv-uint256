import Extracted
import Fv256.MsaCommon
import Fv256.Amd64.MsaDefs
import Fv256.Amd64.MsaBlk0
import Fv256.Amd64.MsaBlk1
import Fv256.Amd64.MsaBlk2
import Fv256.Amd64.MsaBlk3

/-!
# `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` (amd64): the full spec

As the arm64 theorem (`Fv256.Arm64.MarshalSSZAppendMain`): four 8-byte appends, each with its own capacity check and its
own `runtime.growslice` call. Result `(RAX, RBX = len + 32, RCX)` and a nil error (`RDI = RSI = 0`); the bytes
`[len, len + 32)` of the result are the little-endian encoding of `*z`, the first `len` bytes are the old ones, and: if
`len + 32 <= cap` the result is `(dp, len + 32, cap)` and only the 32 bytes (and the stack) change; otherwise the result
array is inside the runtime's ranges `R.rt` and the invariant holds again for a live set containing it.
Runtime assumptions: the `growslice` live contract, `DescOK` for the `uint8` descriptor, the runtime ready for the requests
the code makes (`Ready`) and the budget `4 * Kc len <= b`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)
open Fv256.Msa Fv256.Amd64.Msa

namespace Fv256.Amd64.MarshalSSZAppendMain

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (fun s => StackGuardOK s 4208 ∧ StackWritable s 4208 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧ Buffer s z 32 false ∧
        Apart z.toNat 32 ((s.regs 4).toNat - 4208) 4232 ∧
        Outside ((s.regs 4).toNat - 4208) 4232 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4208) 4232 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 dp.toNat cap.toNat ∧
        R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]) ∧
        (InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt) ∧
        Apart z.toNat 32 dp.toNat cap.toNat ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ dp.toNat + cap.toNat ≤ 2 ^ 48 ∧
        Apart dp.toNat cap.toNat ((s.regs 4).toNat - 4208) 4232 ∧
        Apart u8T 16 ((s.regs 4).toNat - 4208) 4232 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat)
      (fun s s' => AppendPost R s s' z dp.toNat len.toNat cap.toNat b L) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hd, ⟨hz48, hzp⟩, hzd, hout, hga, hgr, hgd, hinv, hLs, hzL, hzpd,
    hlc, hC, hPb, hdj, hdt, hdtd, hdesc, hroom, hgrow, hbud, hrdy⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw := hg.noWrap
  have hgrd := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hgb hnw hgrd hb' ha hw hal hga hgr hgd hzd hout hdt hdtd hdj hinv hLs
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x20]
  trace_state
  sorry

end Fv256.Amd64.MarshalSSZAppendMain
