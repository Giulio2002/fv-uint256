import Extracted

/-!
# Witness for `SetFromDecimal` (amd64), part A: the runtime stand-in and the allocation/copy contracts

Stub code at the contract addresses of `Extracted.program` (newobject, mallocgc, memmove for chunks of 1 … 19 bytes,
gcWriteBarrier1/2) in the toy bump-allocator runtime `R`; every contract is proved by running the stub.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.SetFromDecimal.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def mgA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgc")
def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
abbrev ifA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.ifaceeq")
abbrev cmA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")

/-- the string the witness parses (45 digits) -/
def pSA : Nat := 0x301000

def numErrT : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»

/-- the requests the toy runtime serves: the error-value allocations of `SetFromDecimal` (chunks of 1 … 19 bytes) and the write barriers -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ args = [numErrT]) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2]) ∨
  (a = mgA ∧ ∃ sl, 1 ≤ sl ∧ sl ≤ 19 ∧ args = [sl, 0, 0]) ∨ (a = mvA ∧ ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19)

def R : RtInv := toyR [] ok

/-- the stub runtime: generic code placed at the contract addresses of `Extracted.program` -/
def implA : List Amd64.Segment :=
  [newobjectSeg newA, mallocgcSeg mgA, memmoveUptoSeg64 mvA 19, wbSeg w1A, wbSeg w2A,
   ⟨"witness.ifaceeq", ifA, Janus.Contracts.IfaceSatAmd64.efaceeqCode⟩,
   ⟨"witness.cmpstring", cmA, Janus.Contracts.CmpstringSatAmd64.code⟩]

def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implA }
theorem linked_eq : Extracted.program.link implA = linked := rfl

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_mg : Extracted.program.contractAddr "runtime.mallocgc" = mgA := by decide
theorem addr_mv : Extracted.program.contractAddr "runtime.memmove" = mvA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_if : Extracted.program.contractAddr "runtime.ifaceeq" = ifA := by decide
theorem addr_cm : Extracted.program.contractAddr "runtime.cmpstring" = cmA := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

theorem model_new : NewobjectLiveContract64 (Extracted.program.link implA) newA 4096 R := by rw [linked_eq]; janus64_live_newobject
theorem model_mg : MallocgcLiveContract64 (Extracted.program.link implA) mgA 4096 R := by rw [linked_eq]; janus64_live_mallocgc
theorem hok_mv : ∀ args, ok mvA args → ∃ q p k, args = [q, p, k] ∧ 1 ≤ k ∧ k ≤ 19 := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
  all_goals first | exact h | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A]; decide)
set_option maxHeartbeats 16000000 in
theorem model_mv : MemmoveLive64 (Extracted.program.link implA) mvA 4096 R := by rw [linked_eq]; janus64_live_memmove_upto 19 hok_mv
theorem model_wb1 : WbLiveContract64 (Extracted.program.link implA) w1A 4096 R 1 := by rw [linked_eq]; janus64_live_wb 1
theorem model_wb2 : WbLiveContract64 (Extracted.program.link implA) w2A 4096 R 2 := by rw [linked_eq]; janus64_live_wb 2

end Fv256.Amd64.SetFromDecimal.Witness
