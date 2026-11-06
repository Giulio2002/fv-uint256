import Extracted
import Fv256.MsaCommon

/-!
# `MarshalSSZAppend` (arm64): main statement and witness SKELETON (not compiled yet; the arm64 extraction with the
`runtime.growslice` contract is `build/ex-arm64-MarshalSSZAppend-n`). Mirrors `scratchC/main.tmpl` (amd64); the
block lemmas are `Fv256.Arm64.MarshalSSZAppendG.blk0` (+ generated blk1..3). Hypotheses follow `blk0`'s frame:
stack window `[sp - 4232, sp + 40)`, the stack guard at `g + 16` below `sp - 4224`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa

namespace Fv256.Arm64.MarshalSSZAppendMain

abbrev u8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (fun s => GuardOK s 4224 ∧ StackOK s 4232 40 ∧ s.sp.toNat % 16 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4232) 4272 ∧
        Outside (s.sp.toNat - 4232) 4272 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4232) 4272 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        Apart ((s.regs 28).toNat + 16) 8 dp.toNat cap.toNat ∧
        R.inv b L (s.regs 28).toNat (view R.rt L s.mem) ∧
        (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
        (InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt) ∧
        Apart z.toNat 32 dp.toNat cap.toNat ∧
        len.toNat ≤ cap.toNat ∧ cap.toNat < 2 ^ 40 ∧ dp.toNat + cap.toNat ≤ 2 ^ 48 ∧
        Apart dp.toNat cap.toNat (s.sp.toNat - 4232) 4272 ∧
        Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ Outside u8T 256 R.rt ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧
        Ready R (Extracted.program.contractAddr "runtime.growslice") u8T 4 (len.toNat + 8) cap.toNat)
      (fun s s' => s'.regs 3 = len + 32#64 ∧
        len.toNat + 32 ≤ (s'.regs 2).toNat ∧
        s'.mem.readLE ((s'.regs 0).toNat + len.toNat) 32 = val256 s.mem z.toNat ∧
        (∀ i, i < len.toNat → s'.mem.bytes ((s'.regs 0).toNat + i) = s.mem.bytes (dp.toNat + i)) ∧
        (len.toNat + 32 ≤ cap.toNat → s'.regs 0 = dp ∧ s'.regs 2 = cap ∧
          R.inv b L (s.regs 28).toNat (view R.rt L s'.mem) ∧
          MemFrame s.mem s'.mem [(dp.toNat + len.toNat, dp.toNat + len.toNat + 32),
            (s.sp.toNat - 4232, s.sp.toNat + 40)]) ∧
        (cap.toNat < len.toNat + 32 → InRanges (s'.regs 0).toNat (s'.regs 2).toNat R.rt ∧
          (∃ b' L', R.inv b' L' (s.regs 28).toNat (view R.rt L' s'.mem) ∧
            InRanges (s'.regs 0).toNat (s'.regs 2).toNat L') ∧
          MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40),
            (dp.toNat + len.toNat, dp.toNat + cap.toNat)]))) := by
  sorry

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

/-! The witness is `MarshalSSZAppend(z, nil-array, len 0, cap 32)`: room for all four appends, so no `growslice`
request is made; the runtime serves none (`ok` is false), which satisfies the contract vacuously. The stub runtime
is the generic `growsliceSeg` at `Extracted.program`'s own contract address (size 1 is supported). -/

def u8A : Nat := janus_eval% u8T
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]
def implAt : List Segment := [growsliceSeg grA 0 16 8]
def ok : Nat → List Nat → Prop := fun _ _ => False
def R : RtInv := toyR tys ok
def linked : Program := Extracted.program.link implAt

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 1, 0, 1, (u8A, 1, 0).1] := fun _ h => h.elim

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract linked grA 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (u8A, 1, 0) 1 0 1 16 8 hok_gr

-- GROWTH-PATH WITNESS (pending, per main): a second witness with len = 24, cap = 24 (one growslice call, for the last limb
-- only: len + 8 > cap at block 3) and the stub parameters fixed to that single request
-- `growslice(p, 32, 24, 8, u8)`: `ok := fun a args => a = grA ∧ args = [p0, 32, 24, 8, u8A]`,
-- `janus_live_growslice (u8A, 1, 0) 1 24 8 <A> <cap> hok`, `ob = 24` bytes copied. COVERAGE: "growth-path witness: pending".
-- TODO: state `s0` (sp, g, dst array of 32 writable bytes at dp, z readable), `setup`, `dataLoaded`, `inv0`, `pre`
-- as in examples/rtmisc/proofs/arm64/Push.lean, then
-- `theorem nonvacuous : ∃ impl R b L z dp len cap ret s, RetAddr … ∧ CallSetup … ∧ <the whole precondition>`.

end Witness

end Fv256.Arm64.MarshalSSZAppendMain
