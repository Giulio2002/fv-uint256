import Extracted
import Fv256.Proofs.Arm64.WitModel

/-!
# Witness for `SetFromDecimal` (arm64), part A: the runtime stand-in and the allocation/copy contracts

Stub code at the contract addresses of `Extracted.program` (newobject, mallocgc, memmove for a 1-byte chunk,
gcWriteBarrier1/2) in the toy bump-allocator runtime `R`; every contract is proved by running the stub.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.FdWit

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def mgA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgc")
def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
def ifA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.ifaceeq")
def cmA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")

/-- the type word of `go:itab.internal/strconv.Error,error` (the binary's data names it) -/
def TW : Nat := 0xcfc80

def pSA : Nat := 0x301000
def nSA : Nat := 48

def numErrT : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
def intT : Nat := Extracted.dataAddr.«type:uint256.Int#33f34945»

/-- the requests the toy runtime serves: the allocation of the result `Int`, the error-value allocations of `SetFromDecimal`
(chunks of 1 … 19 bytes), the write barriers -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [numErrT]) ∨ (a = newA ∧ args = [intT]) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2]) ∨
  (a = mgA ∧ ∃ sl, 1 ≤ sl ∧ sl ≤ 19 ∧ args = [sl, 0, 0]) ∨ (a = mvA ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19)

def R : RtInv := toyR [] ok

/-- the stub runtime: generic code placed at the contract addresses of `Extracted.program` -/
def implA : List Segment :=
  [newobjectSeg newA, mallocgcSeg mgA, memmoveUptoSeg mvA 19, wbSeg w1A, wbSeg w2A,
   ⟨"witness.ifaceeq", ifA, Janus.Contracts.IfaceSat.efaceeqCode⟩,
   ⟨"witness.cmpstring", cmA, Janus.Contracts.CmpstringSat.code⟩]

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_mg : Extracted.program.contractAddr "runtime.mallocgc" = mgA := by decide
theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_if : Extracted.program.contractAddr "runtime.ifaceeq" = ifA := by decide
theorem addr_cm : Extracted.program.contractAddr "runtime.cmpstring" = cmA := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

theorem model_new : NewobjectLiveContract (Extracted.program.ofImpl implA) newA 4096 R := by janus_live_newobject
theorem model_mg : MallocgcLiveContract (Extracted.program.ofImpl implA) mgA 4096 R := by janus_live_mallocgc
theorem hok_mv : ∀ args, ok mvA args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19 := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  all_goals first | exact h | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A]; decide)
set_option maxHeartbeats 16000000 in
theorem model_mv : MemmoveLive (Extracted.program.ofImpl implA) mvA 4096 R := by janus_live_memmove_upto 19 hok_mv
theorem model_wb1 : WbLiveContract (Extracted.program.ofImpl implA) w1A 4096 R 1 := by janus_live_wb 1
theorem model_wb2 : WbLiveContract (Extracted.program.ofImpl implA) w2A 4096 R 2 := by janus_live_wb 2

end Fv256.Arm64.FdWit
