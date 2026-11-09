import Extracted

/-!
# Witness for `UnmarshalText` (arm64), part A: the runtime stand-in and the allocation/copy/string contracts

Stub code at the contract addresses of `Extracted.program` in the toy bump-allocator runtime `R`:
`newobject`, `mallocgc`, a variable-size `memmove` (`1 … 19`, the chunk copies of `strconv.ParseUint`'s error value),
`gcWriteBarrier1/2`, and the live `slicebytetostring` for a 48-byte (size class) non-empty string that is copied into a fresh block.
Every contract is proved by running the stub.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.UnmarshalTextWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def mgA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgc")
def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
def ifA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.ifaceeq")
def cmA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")
def sbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.slicebytetostring")

/-- the input string: 48 decimal digits at `pW` -/
def pW : Nat := 0x301000
/-- the second input (48 bytes, a hex string for UnmarshalText, plain digits for UnmarshalJSON) -/
def pH : Nat := 0x302000

def numErrT : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»

/-- the requests the toy runtime serves: the error-value allocations of `SetFromDecimal` (chunks of 1 … 19 bytes), the write
barriers, and `string(input)` for the 48-byte input into either of the two stack buffers -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [numErrT]) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2]) ∨
  (a = mgA ∧ ∃ sl, 1 ≤ sl ∧ sl ≤ 19 ∧ args = [sl, 0, 0]) ∨ (a = mvA ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19) ∨
  (a = sbA ∧ ∃ buf p, args = [buf, p, 48] ∧ (p = pW ∨ p = pH))

def R : RtInv := toyR [] ok

/-- the stub runtime: generic code placed at the contract addresses of `Extracted.program` -/
def implA : List Segment :=
  [newobjectSeg newA, mallocgcSeg mgA, memmoveUptoSeg mvA 19, wbSeg w1A, wbSeg w2A,
   ⟨"witness.ifaceeq", ifA, Janus.Contracts.IfaceSat.efaceeqCode⟩,
   ⟨"witness.cmpstring", cmA, Janus.Contracts.CmpstringSat.code⟩, sbtsSeg sbA 48 48]

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_mg : Extracted.program.contractAddr "runtime.mallocgc" = mgA := by decide
theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_if : Extracted.program.contractAddr "runtime.ifaceeq" = ifA := by decide
theorem addr_cm : Extracted.program.contractAddr "runtime.cmpstring" = cmA := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide
theorem addr_sb : Extracted.program.contractAddr "runtime.slicebytetostring" = sbA := by decide

theorem model_new : NewobjectLiveContract (Extracted.program.ofImpl implA) newA 4096 R := by janus_live_newobject
theorem model_mg : MallocgcLiveContract (Extracted.program.ofImpl implA) mgA 4096 R := by janus_live_mallocgc
theorem hok_mv : ∀ args, ok mvA args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19 := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩
  all_goals first | exact h | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A, sbA]; decide)
set_option maxHeartbeats 16000000 in
theorem model_mv : MemmoveLive (Extracted.program.ofImpl implA) mvA 4096 R := by janus_live_memmove_upto 19 hok_mv
theorem model_wb1 : WbLiveContract (Extracted.program.ofImpl implA) w1A 4096 R 1 := by janus_live_wb 1
theorem model_wb2 : WbLiveContract (Extracted.program.ofImpl implA) w2A 4096 R 2 := by janus_live_wb 2
theorem hok_sb : ∀ args, ok sbA args → ∃ buf ptr, args = [buf, ptr, 48] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, buf, p, rfl, _⟩
  all_goals first | exact ⟨buf, p, rfl⟩ | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A, sbA]; decide)
set_option maxHeartbeats 16000000 in
theorem model_sb : RtLiveContract (Extracted.program.ofImpl implA) sbA 4096 R
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive := by
  janus_live_sbts_big 48 48 hok_sb

end Fv256.Arm64.UnmarshalTextWit
