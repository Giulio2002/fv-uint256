import Extracted
import Fv256.Amd64.ScanCfg

/-!
# Witness for `Scan` (amd64), part A: the runtime stand-in and its contracts

Stub code at the contract addresses of `Extracted.program` in the toy bump-allocator runtime `R`: `newobject`, `mallocgc` (size `1 … 19`),
`memmove` for every size `1 … 19`, the write barriers, `slicebytetostring` for a 48-byte slice, `ifaceeq` (interface model `R0`), `cmpstring`.
Every contract is proved by running the stub.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.Scan.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def mgA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.mallocgc")
def mvA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.memmove")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
abbrev ifA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.ifaceeq")
abbrev cmA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")
def sbA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.slicebytetostring")

/-- the type word of `go:itab.internal/strconv.Error,error` (the binary's data names it) -/
def TW : Nat := 5024992

def numErrT : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
def errT : Nat := Extracted.dataAddr.«type:errors.errorString#8e8100b7»

/-- the requests the toy runtime serves -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ (args = [numErrT] ∨ args = [errT])) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2]) ∨
  (a = mgA ∧ ∃ sl, 1 ≤ sl ∧ sl ≤ 19 ∧ args = [sl, 0, 0]) ∨ (a = mvA ∧ ∃ q p sl, 1 ≤ sl ∧ sl ≤ 19 ∧ args = [q, p, sl]) ∨
  (a = sbA ∧ ∃ buf p, args = [buf, p, 48])

def R : RtInv := toyR [] ok

/-- the stub runtime: generic code placed at the contract addresses of `Extracted.program` -/
def implA : List Amd64.Segment :=
  [newobjectSeg newA, mallocgcSeg mgA, memmoveUptoSeg64 mvA 19, wbSeg w1A, wbSeg w2A, sbtsSeg64 sbA 48 48,
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
theorem addr_sb : Extracted.program.contractAddr "runtime.slicebytetostring" = sbA := by decide

theorem model_new : NewobjectLiveContract64 (Extracted.program.link implA) newA 4096 R := by rw [linked_eq]; janus64_live_newobject
theorem model_mg : MallocgcLiveContract64 (Extracted.program.link implA) mgA 4096 R := by rw [linked_eq]; janus64_live_mallocgc
theorem hok_mv : ∀ args, ok mvA args → ∃ d sr k, args = [d, sr, k] ∧ 1 ≤ k ∧ k ≤ 19 := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, q, p, sl, h1, h2, rfl⟩ | ⟨h, _⟩
  all_goals first | exact ⟨q, p, sl, rfl, h1, h2⟩ | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A, sbA]; decide)
set_option maxHeartbeats 8000000 in
theorem model_mv : MemmoveLive64 (Extracted.program.link implA) mvA 4096 R := by rw [linked_eq]; janus64_live_memmove_upto 19 hok_mv
theorem model_wb1 : WbLiveContract64 (Extracted.program.link implA) w1A 4096 R 1 := by rw [linked_eq]; janus64_live_wb 1
theorem model_wb2 : WbLiveContract64 (Extracted.program.link implA) w2A 4096 R 2 := by rw [linked_eq]; janus64_live_wb 2
theorem hok_sb : ∀ args, ok sbA args → ∃ buf ptr, args = [buf, ptr, 48] := by
  intro args h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, buf, p, h⟩
  all_goals first | exact ⟨buf, p, h⟩ | (exfalso; revert h; simp only [newA, mgA, mvA, w1A, w2A, sbA]; decide)
set_option maxHeartbeats 4000000 in
theorem model_sb : RtLiveContract64 (Extracted.program.link implA) sbA 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)
    slicebytetostringLive := by
  rw [linked_eq]
  janus64_live_sbts_big 48 48 hok_sb

end Fv256.Amd64.Scan.Witness
