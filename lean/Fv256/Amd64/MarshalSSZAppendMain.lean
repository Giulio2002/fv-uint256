import Extracted
import Fv256.Amd64.CallSites.Live
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
        4 * Kc len.toNat ≤ b ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 (len.toNat + 8) cap.toNat)
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
  have hl0b : len.toNat < 2 ^ 40 := by omega
  have hl8 : (len + 8#64).toNat = len.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hl16 : (len + 8#64 + 8#64).toNat = len.toNat + 16 := by rw [BitVec.toNat_add, hl8]; simp; omega
  have hl24 : (len + 8#64 + 8#64 + 8#64).toNat = len.toNat + 24 := by rw [BitVec.toNat_add, hl16]; simp; omega
  refine blk0 impl R ret hret hgs s _ z dp.toNat len.toNat cap.toNat b b len dp cap L L _ hg hal hb' ha hga hgr hgd hzp hz48 hzd hout hdt hdtd hd hdesc
    rfl (by omega) hl0b h_x15 (by first | rfl | decide) 3 ?_
    (fun S1 pp1 cc1 b1 L1 hpc1 hI1 hb1 => blk1 impl R ret hret hgs s S1 z dp.toNat len.toNat cap.toNat b1 b (len + 8#64) pp1 cc1 L1 L _
      hg hal hb' ha hga hgr hgd hzp hz48 hzd hout hdt hdtd hd hdesc (by omega) (by omega) hl0b h_x15 hpc1 2 hI1
      (fun S2 pp2 cc2 b2 L2 hpc2 hI2 hb2 => blk2 impl R ret hret hgs s S2 z dp.toNat len.toNat cap.toNat b2 b (len + 8#64 + 8#64) pp2 cc2 L2 L _
        hg hal hb' ha hga hgr hgd hzp hz48 hzd hout hdt hdtd hd hdesc (by omega) (by omega) hl0b h_x15 hpc2 1 hI2
        (fun S3 pp3 cc3 b3 L3 hpc3 hI3 hb3 => blk3f impl R ret hret hgs s S3 z dp.toNat len.toNat cap.toNat b3 b (len + 8#64 + 8#64 + 8#64) pp3 cc3 L3 L
          hg hal hb' ha hga hgr hgd hzp hz48 hzd hout hdt hdtd hd hdesc (by omega) (by omega) hl0b h_x15 hpc3 0 hI3)))
  have hret47 := hret.user
  have hstk : ∀ a n, ((s.regs 4).toNat - 4208 ≤ a → a + n ≤ (s.regs 4).toNat + 24 → Outside a n R.rt) :=
    fun a n h1 h2 => Outside.of_sub hout (by omega) (by omega)
  have hW : ∀ a n, (s.regs 4).toNat - 4208 ≤ a → a + n ≤ (s.regs 4).toNat + 24 →
      InRanges a n [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp.toNat + len.toNat, dp.toNat + cap.toNat)] :=
    fun a n h1 h2 => ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, h1, h2⟩
  refine ⟨by simp [setRegF], by simp [setRegF, h_a0], by simp [setRegF, h_a1], by simp [setRegF], by simp [setRegF, h_a3],
    by simp [setRegF], by simp [setRegF], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLs, hzL, hzpd, Nat.le_refl _, by omega, hlc, by omega,
    hPb, hdj, ?_, ?_, ?_, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact h_ret
  · simp only []
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := (s.regs 5).isLt; omega)
  · simp only []
    rw [Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by have := z.isLt; omega)
  · simp only [Memory.accessible_writeLE]; exact hw
  · simp only []
    exact (((MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, by omega, by omega⟩
  · intro hc
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only []
    have hW' : ∀ a n, (s.regs 4).toNat - 4208 ≤ a → a + n ≤ (s.regs 4).toNat + 24 →
        InRanges a n [(dp.toNat + len.toNat, dp.toNat + len.toNat), ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)] :=
      fun a n h1 h2 => ⟨((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), by simp, h1, h2⟩
    exact (((MemFrame.refl _ _).writeLE_inRanges _ (hW' _ _ (by omega) (by omega))).writeLE_inRanges _ (hW' _ _ (by omega) (by omega))).writeLE_inRanges _
      (hW' _ _ (by omega) (by omega))
  · intro i hi
    simp only []
    unfold Apart at hzd
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  · simp only []
    rw [view_writeLE_out (hstk _ _ (by omega) (by omega)), view_writeLE_out (hstk _ _ (by omega) (by omega)),
      view_writeLE_out (hstk _ _ (by omega) (by omega))]
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
      Memory.bytes_writeLE_outside _ (by omega)]
  · simp


namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

/-- The witness is `MarshalSSZAppend(z, dp, len = 0, cap = 32)`: room for all four limbs, so no `growslice` request is made
(the runtime serves none: `ok` is false) and the contract holds vacuously at the generic stub runtime. -/
def u8A : Nat := janus_eval% u8T
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]
def implAt : List Amd64.Segment := [growsliceSeg grA 32 64 64]
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]
def R : RtInv := toyR tys ok
def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem ut_eq : u8T = u8A := by decide

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract64 linked grA 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zA : Nat := 0x300000
def dpA : Nat := 0x310000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Arm64.Memory :=
  ⟨bytes0, [⟨sp0 - 4208, 4232, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨zA, 32, false⟩, ⟨dpA, 32, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def dpV : BitVec 64 := BitVec.ofNat 64 dpA

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then dpV else if i = 7 then 32 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, dpV, 0, 32] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
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

theorem inv0 : R.inv 0x1000 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

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


theorem pre : StackGuardOK s0 4208 ∧ StackWritable s0 4208 24 ∧ (s0.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s0.mem ∧ Buffer s0 zV 32 false ∧
        Apart zV.toNat 32 ((s0.regs 4).toNat - 4208) 4232 ∧
        Outside ((s0.regs 4).toNat - 4208) 4232 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4208) 4232 ∧
        Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 dpV.toNat (32 : BitVec 64).toNat ∧
        R.inv 0x1000 ([] : List (Nat × Nat)) (s0.regs 14).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s0.regs 4).toNat - 4208, (s0.regs 4).toNat + 24)]) ∧
        (InRanges zV.toNat 32 ([] : List (Nat × Nat)) ∨ Outside zV.toNat 32 R.rt) ∧
        Apart zV.toNat 32 dpV.toNat (32 : BitVec 64).toNat ∧
        (0 : BitVec 64).toNat ≤ (32 : BitVec 64).toNat ∧ (32 : BitVec 64).toNat < 2 ^ 40 ∧ dpV.toNat + (32 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart dpV.toNat (32 : BitVec 64).toNat ((s0.regs 4).toNat - 4208) 4232 ∧
        Apart u8T 16 ((s0.regs 4).toNat - 4208) 4232 ∧ Apart u8T 16 dpV.toNat (32 : BitVec 64).toNat ∧ DescOK R u8T ∧
        ((0 : BitVec 64).toNat + 8 ≤ (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat true = true ∧
          (InRanges dpV.toNat (32 : BitVec 64).toNat ([] : List (Nat × Nat)) ∨ Outside dpV.toNat (32 : BitVec 64).toNat R.rt)) ∧
        ((32 : BitVec 64).toNat < (0 : BitVec 64).toNat + 8 → (0 < (0 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (0 : BitVec 64).toNat false = true)) ∧
        4 * Kc (0 : BitVec 64).toNat ≤ 0x1000 ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 ((0 : BitVec 64).toNat + 8) (32 : BitVec 64).toNat := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ⟨by decide, by decide⟩,
    by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, inv0,
    fun r hr => absurd hr (by simp), Or.inr ?_, by simp only [Apart]; decide, by decide, by decide, by decide,
    by simp only [Apart]; decide, ?_, ?_, descOK', fun _ => ⟨by decide, Or.inr ?_⟩,
    fun h => absurd h (by decide), by decide, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · simp [Fv256.Amd64.Msa.Ready]

-- CALLSITE-BLOCK w1
def csG0 : Amd64.State :=
  { s0 with regs := fun i => if i = 0 then dpV else if i = 3 then 40 else if i = 1 then 32 else if i = 7 then 8 else if i = 6 then BitVec.ofNat 64 u8A else if i = 4 then BitVec.ofNat 64 (sp0 - 64) else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `RSP = sp0 - 64`. -/
def csG : Amd64.State := { csG0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

theorem csG_rip : csG.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  have hw : argWords64 csG 5 = [dpA, 40, 32, 8, u8A] := by
    unfold argWords64 csG csG0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, hw, Contracts.arg]
    exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside, hw]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide)
  · rw [hw, addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget, a live set and a call of
`MarshalSSZAppend(z, dp, 0, 32)` satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64)
    (ret : Nat) (s : State),
    RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (StackGuardOK s 4208 ∧ StackWritable s 4208 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
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
        4 * Kc len.toNat ≤ b ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 (len.toNat + 8) cap.toNat) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ AppendPost R s s' z dp.toNat len.toNat cap.toNat b L := by
  refine ⟨implAt, R, 0x1000, [], zV, dpV, 0, 32, ret, s0, ?w0, hret, setup, pre,
    ⟨csG, csG_rip, csG_pre⟩,
    correctness implAt R 0x1000 ([]) zV dpV 0 32 ?w0 ret hret s0 setup pre⟩
  case w0 => exact by rw [addr_gr]; exact model_gr
end Witness

namespace Grow.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

/-- The witness is `MarshalSSZAppend(z, dp, len = 0, cap = 32)`: room for all four limbs, so no `growslice` request is made
(the runtime serves none: `ok` is false) and the contract holds vacuously at the generic stub runtime. -/
def u8A : Nat := janus_eval% u8T
def grA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.growslice")
def tys : Tys := [(u8A, 1, 0)]
def implAt : List Amd64.Segment := [growsliceSeg grA 32 64 64]
def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]
def R : RtInv := toyR tys ok
def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_gr : Extracted.program.contractAddr "runtime.growslice" = grA := by decide
theorem ut_eq : u8T = u8A := by decide

theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2

set_option maxHeartbeats 4000000 in
theorem model_gr : RtLiveContract64 linked grA 4096 R growsliceSpec growsliceLive := by
  janus64_live_growslice (u8A, 1, 0) 40 32 8 64 64 hok_gr

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zA : Nat := 0x300000
def dpA : Nat := 0x310000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Arm64.Memory :=
  ⟨bytes0, [⟨sp0 - 4208, 4232, true⟩, ⟨g0, 0x100, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨zA, 32, false⟩, ⟨dpA, 32, true⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def dpV : BitVec 64 := BitVec.ofNat 64 dpA

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then dpV else if i = 1 then 32 else if i = 7 then 32 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, dpV, 32, 32] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl, rfl⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
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

theorem inv0 : R.inv 0x1000 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init_tys tysOK (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide)
    (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

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


theorem pre : StackGuardOK s0 4208 ∧ StackWritable s0 4208 24 ∧ (s0.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s0.mem ∧ Buffer s0 zV 32 false ∧
        Apart zV.toNat 32 ((s0.regs 4).toNat - 4208) 4232 ∧
        Outside ((s0.regs 4).toNat - 4208) 4232 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4208) 4232 ∧
        Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
        Apart ((s0.regs 14).toNat + 16) 8 dpV.toNat (32 : BitVec 64).toNat ∧
        R.inv 0x1000 ([] : List (Nat × Nat)) (s0.regs 14).toNat (view R.rt ([] : List (Nat × Nat)) s0.mem) ∧
        (∀ r ∈ ([] : List (Nat × Nat)), Outside r.1 (r.2 - r.1) [((s0.regs 4).toNat - 4208, (s0.regs 4).toNat + 24)]) ∧
        (InRanges zV.toNat 32 ([] : List (Nat × Nat)) ∨ Outside zV.toNat 32 R.rt) ∧
        Apart zV.toNat 32 dpV.toNat (32 : BitVec 64).toNat ∧
        (32 : BitVec 64).toNat ≤ (32 : BitVec 64).toNat ∧ (32 : BitVec 64).toNat < 2 ^ 40 ∧ dpV.toNat + (32 : BitVec 64).toNat ≤ 2 ^ 48 ∧
        Apart dpV.toNat (32 : BitVec 64).toNat ((s0.regs 4).toNat - 4208) 4232 ∧
        Apart u8T 16 ((s0.regs 4).toNat - 4208) 4232 ∧ Apart u8T 16 dpV.toNat (32 : BitVec 64).toNat ∧ DescOK R u8T ∧
        ((32 : BitVec 64).toNat + 8 ≤ (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat true = true ∧
          (InRanges dpV.toNat (32 : BitVec 64).toNat ([] : List (Nat × Nat)) ∨ Outside dpV.toNat (32 : BitVec 64).toNat R.rt)) ∧
        ((32 : BitVec 64).toNat < (32 : BitVec 64).toNat + 8 → (0 < (32 : BitVec 64).toNat → s0.mem.accessible dpV.toNat (32 : BitVec 64).toNat false = true)) ∧
        4 * Kc (32 : BitVec 64).toNat ≤ 0x1000 ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 ((32 : BitVec 64).toNat + 8) (32 : BitVec 64).toNat := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ⟨by decide, by decide⟩,
    by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, ?_, by simp only [Apart]; decide, inv0,
    fun r hr => absurd hr (by simp), Or.inr ?_, by simp only [Apart]; decide, by decide, by decide, by decide,
    by simp only [Apart]; decide, ?_, ?_, descOK', fun h => absurd h (by decide),
    fun _ _ => by decide, by decide, ?_⟩
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · rw [ut_eq]; simp only [Apart]; decide
  · have hgc : growCap 1 true 40 32 = 64 := by decide
    simp [Fv256.Amd64.Msa.Ready, hgc, ut_eq]
    intro p
    exact ⟨rfl, p, rfl⟩

-- CALLSITE-BLOCK w2
def csG0 : Amd64.State :=
  { s0 with regs := fun i => if i = 0 then dpV else if i = 3 then 40 else if i = 1 then 32 else if i = 7 then 8 else if i = 6 then BitVec.ofNat 64 u8A else if i = 4 then BitVec.ofNat 64 (sp0 - 64) else s0.regs i }
/-- The call state of `runtime.growslice` (U-WITNESS-CALLSITE): `growslice(dp, 40, 32, 8, uint8)` at its entry, `RSP = sp0 - 64`. -/
def csG : Amd64.State := { csG0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") }

theorem csG_rip : csG.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csG_pre : RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 csG := by
  have hw : argWords64 csG 5 = [dpA, 40, 32, 8, u8A] := by
    unfold argWords64 csG csG0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, by simp only [calleeStack64, outside_cons, outside_nil]; decide⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [growsliceSpec, hw, Contracts.arg]
    exact ⟨⟨by decide, by decide, by decide⟩, by decide, by decide, by decide, by decide, ⟨by decide, fun _ => by decide⟩⟩
  · simp only [growsliceSpec, ReadsOutside, hw]
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide)
  · rw [hw, addr_gr]; exact ⟨rfl, dpA, by decide⟩
  · intro r hr
    rw [rt_eq]
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_append, outside_cons, outside_nil]; decide)

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget, a live set and a call of
`MarshalSSZAppend(z, dp, 32, 32)` (one growslice request) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (L : List (Nat × Nat)) (z dp len cap : BitVec 64)
    (ret : Nat) (s : State),
    RtLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, dp, len, cap] s ∧
    (StackGuardOK s 4208 ∧ StackWritable s 4208 24 ∧ (s.regs 4).toNat % 8 = 0 ∧
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
        4 * Kc len.toNat ≤ b ∧ Fv256.Amd64.Msa.Ready R ga u8T 4 (len.toNat + 8) cap.toNat) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.growslice") ∧ RtLivePre64 4096 R growsliceSpec growsliceLive (Extracted.program.contractAddr "runtime.growslice") [] 0x1000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ AppendPost R s s' z dp.toNat len.toNat cap.toNat b L := by
  refine ⟨implAt, R, 0x1000, [], zV, dpV, 32, 32, ret, s0, ?w0, hret, setup, pre,
    ⟨csG, csG_rip, csG_pre⟩,
    correctness implAt R 0x1000 ([]) zV dpV 32 32 ?w0 ret hret s0 setup pre⟩
  case w0 => exact by rw [addr_gr]; exact model_gr
end Grow.Witness

end Fv256.Amd64.MarshalSSZAppendMain
