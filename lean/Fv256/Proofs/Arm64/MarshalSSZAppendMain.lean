import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.MsaCommon
import Fv256.Proofs.Arm64.MarshalSSZAppendG
import Fv256.Proofs.Arm64.MsaBlk1
import Fv256.Proofs.Arm64.MsaBlk2
import Fv256.Proofs.Arm64.MsaBlk3

/-!
# `(*uint256.Int).MarshalSSZAppend(dst []byte) ([]byte, error)` (arm64): the full spec

`dst = append(dst, z[0..3] little-endian)` as four 8-byte appends, each with its own capacity check and its own
`runtime.growslice(p, n, c, 8, uint8)` call. Result `(x0, len + 32, x2)` and a nil error (`x3 = x4 = 0`); the bytes
`[len, len + 32)` of the result are the little-endian encoding of `*z`, the first `len` bytes are the old ones, and:
if `len + 32 <= cap` the result is `(dp, len + 32, cap)` and only the 32 bytes (and the stack) change; otherwise the
result array is inside the runtime's ranges `R.rt` and the invariant holds again for a live set containing it.
Runtime assumptions: the `growslice` live contract, `DescOK` for the `uint8` descriptor, the runtime ready for the
requests the code makes (`Ready`) and the budget `4 * Kc len <= b`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Msa Fv256.Arm64.MarshalSSZAppendG

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MarshalSSZAppendMain

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat))
    (z dp len cap : BitVec 64)
    (hgs : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, dp, len, cap]
      (fun s => GuardOK s 4224 ∧ StackOK s 4232 40 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
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
        Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat)
      (fun s s' => AppendPost R s s' z dp.toNat len.toNat cap.toNat b L) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, ⟨hzp, hz48⟩, hzd, hout, hga, hgr, hgd, hinv, hLs, hzL, hzpd,
    hlc, hC, hPb, hdj, hdt, hdtd, hdesc, hroom, hgrow, hbud, hrdy⟩
  janus_intro hs
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x24]
  have hl0b : len.toNat < 2 ^ 40 := by omega
  have hl8 : (len + 8#64).toNat = len.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hl16 : (len + 8#64 + 8#64).toNat = len.toNat + 16 := by rw [BitVec.toNat_add, hl8]; simp; omega
  have hl24 : (len + 8#64 + 8#64 + 8#64).toNat = len.toNat + 24 := by rw [BitVec.toNat_add, hl16]; simp; omega
  refine blk0 impl R ret hret hgs s _ z dp.toNat len.toNat cap.toNat b b len dp cap L L _ hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc
    rfl (by omega) hl0b (by first | rfl | decide) 3 ?_
    (fun S1 pp1 cc1 b1 L1 hpc1 hI1 hb1 => blk1 impl R ret hret hgs s S1 z dp.toNat len.toNat cap.toNat b1 b (len + 8#64) pp1 cc1 L1 L _
      hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc1 2 hI1
      (fun S2 pp2 cc2 b2 L2 hpc2 hI2 hb2 => blk2 impl R ret hret hgs s S2 z dp.toNat len.toNat cap.toNat b2 b (len + 8#64 + 8#64) pp2 cc2 L2 L _
        hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc2 1 hI2
        (fun S3 pp3 cc3 b3 L3 hpc3 hI3 hb3 => blk3f impl R ret hret hgs s S3 z dp.toNat len.toNat cap.toNat b3 b (len + 8#64 + 8#64 + 8#64) pp3 cc3 L3 L
          hal hb' ha hg1 hg2 hg3 hzp hz48 hzd hout hga hgr hdt hgd hdtd hd hdesc (by omega) (by omega) hl0b hpc3 0 hI3)))
  have hret48 := hret.user
  have hstk : ∀ a n, (s.sp.toNat - 4232 ≤ a → a + n ≤ s.sp.toNat + 40 → Outside a n R.rt) :=
    fun a n h1 h2 => Outside.of_sub hout (by omega) (by omega)
  refine ⟨rfl, by simp [setReg, h_x0], by simp [setReg, h_x1], by simp [setReg, h_x3], by simp [setReg], by simp [setReg],
    by simp [setReg], by simp [setReg], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLs, hzL, hzpd, Nat.le_refl _, by omega, hlc, by omega, hPb, hdj,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 29).isLt; omega)
  · simp only []
    rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := z.isLt; omega)
  · simp only [Memory.accessible_writeLE]; exact hw
  · simp only []
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
  · intro hc
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only []
    exact ((((MemFrame.refl _ _).writeLE_inRanges _ ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨(s.sp.toNat - 4232, s.sp.toNat + 40), by simp, by omega, by omega⟩
  · intro i hi
    simp only []
    unfold Disjoint at hzd
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · simp only []
    rw [view_writeLE_out (hstk _ _ (by omega) (by omega)), view_writeLE_out (hstk _ _ (by omega) (by omega)),
      view_writeLE_out (hstk _ _ (by omega) (by omega)), view_writeLE_out (hstk _ _ (by omega) (by omega))]
    exact hinv
  · intro h
    simp only [Memory.accessible_writeLE]; exact hroom h
  · intro h h0
    simp only [Memory.accessible_writeLE]; exact hgrow h h0
  · simpa using hbud
  · exact hrdy
  · intro i hi
    simp only []
    unfold Apart at hdj
    rw [Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega),
      Memory.bytes_writeLE_outside _ (by omega), Memory.bytes_writeLE_outside _ (by omega)]
  · simp


namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

/-- The witness is `MarshalSSZAppend(z, dp, len = 0, cap = 32)`: room for all four limbs, so no `growslice` request is made by the code;
the stub runtime serves the request `growslice(p, 40, 32, 8, uint8)` (as in `Grow.Witness`) so that the call-site state exists. -/
def u8A : Nat := janus_eval% u8T
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]
def implAt : List Segment := [growsliceSeg grA 32 64 64]
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]
def R : RtInv := toyR tys ok
def linked : Program := Extracted.program.link implAt

theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem ut_eq : u8T = u8A := by decide

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract linked grA 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zA : Nat := 0x300000
def dpA : Nat := 0x310000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4232, 4272, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨zA, 32, false⟩, ⟨dpA, 32, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def dpV : BitVec 64 := BitVec.ofNat 64 dpA

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 1 then dpV else if i = 3 then 32 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, dpV, 0, 32] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem tysOK : TysOK tys := by decide

open Janus.Contracts.PoolSat (toyInv_init_tys)

theorem inv0 : R.inv 0x1000 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] ++ [(u8A, u8A + 16)] := rfl

/-- `DescOK` for the toy runtime: its invariant carries the descriptor words, and the live objects lie in the heap. -/
theorem descOK : DescOK R u8A := by
  right
  intro b L g m hinv
  obtain ⟨p, -, hH, -, -, hL, -, -, -, -, hT⟩ := hinv
  have hmem : (u8A, 1, 0) ∈ tys := by simp [tys]
  have hd := hT _ hmem
  have hh := (tysOK.heap hmem)
  have hOutL : Outside u8A 16 L := Toy.outside_of_forall fun r hr => Or.inl (by have := (hL r hr).1; simp only at hh ⊢; omega)
  have hIn : InRanges u8A 16 R.rt := ⟨(u8A, u8A + 16), by simp [R, toyR, toyRt, tys], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨?_, ?_⟩
  · rw [← readLE_view (rt := R.rt) (L := L) (m := m) (hIn.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hOutL (Nat.le_refl _) (by omega))]
    exact hd.1
  · rw [← readLE_view (rt := R.rt) (L := L) (m := m) (hIn.sub (by omega) (by omega)) (Outside.of_sub hOutL (by omega) (by omega))]
    exact hd.2

theorem descOK' : DescOK R u8T := by rw [ut_eq]; exact descOK


theorem pre : GuardOK s0 4224 ∧ StackOK s0 4232 40 ∧ Extracted.program.DataLoaded s0.mem ∧ Ptr32 s0.mem zV false ∧
        Disjoint zV.toNat 32 (s0.sp.toNat - 4232) 4272 ∧
        Outside (s0.sp.toNat - 4232) 4272 R.rt ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4232) 4272 ∧
        Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧
        Apart ((s0.regs 28).toNat + 16) 8 dpV.toNat (32 : BitVec 64).toNat ∧
        R.inv 0x1000 ([] : List (Nat × Nat)) (s0.regs 28).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [(s0.sp.toNat - 4232, s0.sp.toNat + 40)]) ∧
        (InRanges zV.toNat 32 ([] : List (Nat × Nat)) ∨ Outside zV.toNat 32 R.rt) ∧
        Apart zV.toNat 32 dpV.toNat (32 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat ≤ (32 : BitVec 64).toNat ∧ (32 : BitVec 64).toNat < 2 ^ 40 ∧ dpV.toNat + (32 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart dpV.toNat (32 : BitVec 64).toNat (s0.sp.toNat - 4232) 4272 ∧
        Apart u8T 16 (s0.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dpV.toNat (32 : BitVec 64).toNat ∧ DescOK R u8T ∧
        ((0 : BitVec 64).toNat + 8 ≤ (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat true = true ∧
          (InRanges dpV.toNat (32 : BitVec 64).toNat ([] : List (Nat × Nat)) ∨ Outside dpV.toNat (32 : BitVec 64).toNat R.rt)) ∧
        ((32 : BitVec 64).toNat < (0 : BitVec 64).toNat + 8 → (0 < (0 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (0 : BitVec 64).toNat false = true)) ∧
        4 * Kc (0 : BitVec 64).toNat ≤ 0x1000 ∧ Ready R ga u8T 4 ((0 : BitVec 64).toNat + 8) (32 : BitVec 64).toNat := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, ?_, by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, inv0,
    fun r hr => absurd hr (by simp), Or.inr ?_, by simp only [Apart]; decide, by decide, by decide, by decide,
    by simp only [Apart]; decide, ?_, ?_, descOK', fun _ => ⟨by decide, Or.inr ?_⟩,
    fun h => absurd h (by decide), by decide, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · simp [Fv256.Msa.Ready]

-- CALLSITE-BLOCK w1
def csG0 : State := { s0 with regs := fun i => if i = 0 then dpV else if i = 1 then 40 else if i = 2 then 32 else if i = 3 then 8 else if i = 4 then BitVec.ofNat 64 u8A else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `SP = sp0 - 128`. -/
def csG : State := { csG0 with sp := BitVec.ofNat 64 (sp0 - 128), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, argWords, wordsFrom, arg]
    exact ⟨⟨typeOK_of (by decide) (by decide), by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [argWords, wordsFrom, arg, Outside, calleeStack]; decide)
  · rw [addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget, a live set and a call of
`MarshalSSZAppend(z, dp, 0, 32)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64)
    (ret : Nat) (s : State),
    RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (GuardOK s 4224 ∧ StackOK s 4232 40 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
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
        Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ AppendPost R s s' z dp.toNat len.toNat cap.toNat b L := by
  refine ⟨implAt, R, 0x1000, [], zV, dpV, 0, 32, ret, s0, ?w0, hret, setup, pre,
    ⟨csG, rfl, csG_pre⟩,
    correctness implAt R 0x1000 ([]) zV dpV 0 32 ?w0 ret hret s0 setup pre⟩
  case w0 => exact by rw [addr_gr]; exact model_gr
end Witness

namespace Grow.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

/-- The witness is `MarshalSSZAppend(z, dp, len = 0, cap = 32)`: room for all four limbs, so no `growslice` request is made
(the runtime serves none: `ok` is false) and the contract holds vacuously at the generic stub runtime. -/
def u8A : Nat := janus_eval% u8T
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]
def implAt : List Segment := [growsliceSeg grA 32 64 64]
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]
def R : RtInv := toyR tys ok
def linked : Program := Extracted.program.link implAt

theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem ut_eq : u8T = u8A := by decide

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract linked grA 4096 R growsliceSpec growsliceLive := by
  janus_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zA : Nat := 0x300000
def dpA : Nat := 0x310000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4232, 4272, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨zA, 32, false⟩, ⟨dpA, 32, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def dpV : BitVec 64 := BitVec.ofNat 64 dpA

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 1 then dpV else if i = 2 then 32 else if i = 3 then 32 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, dpV, 32, 32] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem tysOK : TysOK tys := by decide

open Janus.Contracts.PoolSat (toyInv_init_tys)

theorem inv0 : R.inv 0x1000 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] ++ [(u8A, u8A + 16)] := rfl

/-- `DescOK` for the toy runtime: its invariant carries the descriptor words, and the live objects lie in the heap. -/
theorem descOK : DescOK R u8A := by
  right
  intro b L g m hinv
  obtain ⟨p, -, hH, -, -, hL, -, -, -, -, hT⟩ := hinv
  have hmem : (u8A, 1, 0) ∈ tys := by simp [tys]
  have hd := hT _ hmem
  have hh := (tysOK.heap hmem)
  have hOutL : Outside u8A 16 L := Toy.outside_of_forall fun r hr => Or.inl (by have := (hL r hr).1; simp only at hh ⊢; omega)
  have hIn : InRanges u8A 16 R.rt := ⟨(u8A, u8A + 16), by simp [R, toyR, toyRt, tys], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨?_, ?_⟩
  · rw [← readLE_view (rt := R.rt) (L := L) (m := m) (hIn.sub (Nat.le_refl _) (by omega)) (Outside.of_sub hOutL (Nat.le_refl _) (by omega))]
    exact hd.1
  · rw [← readLE_view (rt := R.rt) (L := L) (m := m) (hIn.sub (by omega) (by omega)) (Outside.of_sub hOutL (by omega) (by omega))]
    exact hd.2

theorem descOK' : DescOK R u8T := by rw [ut_eq]; exact descOK


theorem pre : GuardOK s0 4224 ∧ StackOK s0 4232 40 ∧ Extracted.program.DataLoaded s0.mem ∧ Ptr32 s0.mem zV false ∧
        Disjoint zV.toNat 32 (s0.sp.toNat - 4232) 4272 ∧
        Outside (s0.sp.toNat - 4232) 4272 R.rt ∧
        Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4232) 4272 ∧
        Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧
        Apart ((s0.regs 28).toNat + 16) 8 dpV.toNat (32 : BitVec 64).toNat ∧
        R.inv 0x1000 ([] : List (Nat × Nat)) (s0.regs 28).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [(s0.sp.toNat - 4232, s0.sp.toNat + 40)]) ∧
        (InRanges zV.toNat 32 ([] : List (Nat × Nat)) ∨ Outside zV.toNat 32 R.rt) ∧
        Apart zV.toNat 32 dpV.toNat (32 : BitVec 64).toNat ∧
        (32 : BitVec 64).toNat ≤ (32 : BitVec 64).toNat ∧ (32 : BitVec 64).toNat < 2 ^ 40 ∧ dpV.toNat + (32 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart dpV.toNat (32 : BitVec 64).toNat (s0.sp.toNat - 4232) 4272 ∧
        Apart u8T 16 (s0.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dpV.toNat (32 : BitVec 64).toNat ∧ DescOK R u8T ∧
        ((32 : BitVec 64).toNat + 8 ≤ (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat true = true ∧
          (InRanges dpV.toNat (32 : BitVec 64).toNat ([] : List (Nat × Nat)) ∨ Outside dpV.toNat (32 : BitVec 64).toNat R.rt)) ∧
        ((32 : BitVec 64).toNat < (32 : BitVec 64).toNat + 8 → (0 < (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat false = true)) ∧
        4 * Kc (32 : BitVec 64).toNat ≤ 0x1000 ∧ Ready R ga u8T 4 ((32 : BitVec 64).toNat + 8) (32 : BitVec 64).toNat := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ⟨by decide, by decide⟩,
    by unfold Disjoint; decide, ?_, by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, inv0,
    fun r hr => absurd hr (by simp), Or.inr ?_, by simp only [Apart]; decide, by decide, by decide, by decide,
    by simp only [Apart]; decide, ?_, ?_, descOK', fun h => absurd h (by decide),
    fun _ _ => by decide, by decide, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · have hgc : growCap 1 true 40 32 = 64 := by decide
    simp [Fv256.Msa.Ready, hgc, ut_eq]
    intro p
    exact ⟨rfl, p, rfl⟩

-- CALLSITE-BLOCK w2
def csG0 : State := { s0 with regs := fun i => if i = 0 then dpV else if i = 1 then 40 else if i = 2 then 32 else if i = 3 then 8 else if i = 4 then BitVec.ofNat 64 u8A else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `SP = sp0 - 128`. -/
def csG : State := { csG0 with sp := BitVec.ofNat 64 (sp0 - 128), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, argWords, wordsFrom, arg]
    exact ⟨⟨typeOK_of (by decide) (by decide), by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [argWords, wordsFrom, arg, Outside, calleeStack]; decide)
  · rw [addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget, a live set and a call of
`MarshalSSZAppend(z, dp, 32, 32)` (one growslice request) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64)
    (ret : Nat) (s : State),
    RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (GuardOK s 4224 ∧ StackOK s 4232 40 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem z false ∧
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
        Apart u8T 16 (s.sp.toNat - 4232) 4272 ∧ Apart u8T 16 dp.toNat cap.toNat ∧ DescOK R u8T ∧
        (len.toNat + 8 ≤ cap.toNat → s.mem.accessible dp.toNat cap.toNat true = true ∧
          (InRanges dp.toNat cap.toNat L ∨ Outside dp.toNat cap.toNat R.rt)) ∧
        (cap.toNat < len.toNat + 8 → (0 < len.toNat → s.mem.accessible dp.toNat len.toNat false = true)) ∧
        4 * Kc len.toNat ≤ b ∧ Ready R ga u8T 4 (len.toNat + 8) cap.toNat) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ AppendPost R s s' z dp.toNat len.toNat cap.toNat b L := by
  refine ⟨implAt, R, 0x1000, [], zV, dpV, 32, 32, ret, s0, ?w0, hret, setup, pre,
    ⟨csG, rfl, csG_pre⟩,
    correctness implAt R 0x1000 ([]) zV dpV 32 32 ?w0 ret hret s0 setup pre⟩
  case w0 => exact by rw [addr_gr]; exact model_gr
end Grow.Witness

end Fv256.Arm64.MarshalSSZAppendMain
