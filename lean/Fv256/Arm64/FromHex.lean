import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.SetFromHexLoops
import Fv256.Arm64.FromHexCommon

/-!
# `uint256.FromHex(hex string) (*Int, error)` (arm64)

`var z Int` escapes, so the compiled code calls `runtime.newobject` (pinned `NewobjectContract`) and then the non-inlined
`fromHex` (callee summary `SetFromHexLoops.fromHex_sum`, specification `Fv256.C.parseHex`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Arm64.SetFromHexLoops Fv256.Arm64.FromHexCommon

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.FromHex

/-- the type descriptor `FromHex` passes to `runtime.newobject` (`uint256.Int`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.FromHex" 8)
    (segWord Extracted.program "github.com/holiman/uint256.FromHex" 9) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [hp, len]
      (fun s => GuardOK s 48 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        Ptr s.mem hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
        Disjoint hp.toNat len.toNat (s.sp.toNat - 4144) 4168 ∧
        s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Outside errBase 96 rt ∧ Disjoint errBase 96 (s.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
        Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168)
      (fun s s' =>
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 2 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hfp, hH, ⟨hps, hps'⟩, hout1, hd1, herr, hnn, hout2, hd2, hout3, hout4, hd4⟩
  simp only [errBase_val, tabBase_val] at *
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hd4
  janus_run until [Extracted.entry + 0x2c] calls [hnew.pos]
  rename_i wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr
  have htb : ∀ c, c < 256 → s.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255 := tab_vals hd
  have e1 := InRanges.disjoint hin hout3
  have e2 := InRanges.disjoint hin hout1
  have e3 := InRanges.disjoint hin hout
  have e4 := InRanges.disjoint hin hout2
  have f1 : ∀ c, c < 256 → (we.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat wa)).readLE (1002789 + c) 1 =
      (hexNib c).getD 255 := by
    intro c hc
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [hfr.readLE (1002789 + c) 1 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout3 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact htb c hc
  have f2 : ∀ e, e < 6 → ¬ (we.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat wa)).readLE (errAddrOf e) 8 = 0 := by
    intro e he
    have hb := errAddrOf_bounds e
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [hfr.readLE (errAddrOf e) 8 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    exact hnn e he
  have hB : parseHex (bytesAt (we.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat wa)) hp.toNat) len.toNat =
      parseHex (bytesAt s.mem hp.toNat) len.toNat := by
    apply parseHex_congr
    intro k hk
    unfold bytesAt
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    rw [hfr.readLE (hp.toNat + k) 1 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout1 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hEE : ∀ e, e < 6 → ((we.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat wa)).readLE (errAddrOf e) 8 =
      s.mem.readLE (errAddrOf e) 8) ∧
      ((we.writeLE (BitVec.toNat s.sp - 16) 8 (BitVec.toNat wa)).readLE (errAddrOf e + 8) 8 =
      s.mem.readLE (errAddrOf e + 8) 8) := by
    intro e he
    have hb := errAddrOf_bounds e
    constructor
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ 8 (by
        rw [outside_append]
        refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
        simp only [outside_cons, outside_nil]
        refine ⟨?_, ?_, trivial⟩ <;> omega)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      rw [hfr.readLE _ 8 (by
        rw [outside_append]
        refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
        simp only [outside_cons, outside_nil]
        refine ⟨?_, ?_, trivial⟩ <;> omega)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
  have hx29 : BitVec.ofNat 64 (BitVec.toNat s.sp - 8) = s.sp - 8#64 :=
    Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb)
  have hnz : ∀ e, e < 6 → BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ≠ 0 := by
    intro e he h0
    apply hnn e he
    have h2 : (BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8)).toNat = 0 := by rw [h0]; rfl
    rw [BitVec.toNat_ofNat] at h2
    have h1 := Memory.readLE_lt s.mem (errAddrOf e) 8
    have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8] at h1
    omega
  have hA : MemFrame s.mem ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat s.sp - 8)).writeLE (BitVec.toNat s.sp + 16) 8 len.toNat).writeLE (BitVec.toNat s.sp + 8) 8 hp.toNat)
      [(BitVec.toNat s.sp - 4144, BitVec.toNat s.sp + 24)] := by
    refine (((MemFrame.refl s.mem _).writeLE _ (r := (BitVec.toNat s.sp - 4144, BitVec.toNat s.sp + 24)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := (BitVec.toNat s.sp - 4144, BitVec.toNat s.sp + 24))
      (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _
      (r := (BitVec.toNat s.sp - 4144, BitVec.toNat s.sp + 24)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega) |>.writeLE _ (r := (BitVec.toNat s.sp - 4144, BitVec.toNat s.sp + 24)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)
  janus_run calls [fromHex_summary impl hp len]
  all_goals
    rename_i hguard hpcA hpcB hsp h28 h29 h30 h18 hE hfr2 hOK
    rw [hB] at hE hOK
    first
    | (refine ⟨hx29, ?_, ?_, ?_⟩
       · intro v hv
         obtain ⟨a, b, c⟩ := hOK v hv
         exact ⟨BitVec.toNat wa, rfl, hin, h16, hacc, c⟩
       · intro e he
         exfalso
         have h0 := (hE e he).1
         have hlt := parseHex_error_lt _ _ _ he
         rw [(hEE e hlt).1] at h0
         have h00 : s'.regs 0 = 0 := BitVec.eq_of_toNat_eq (by simpa using hbr)
         rw [h00] at h0
         exact hnz e hlt h0.symm
       · exact frame_comp s.mem _ we s'.mem rt (BitVec.toNat s.sp) (BitVec.toNat wa) (BitVec.toNat wa) hb hin hA hfr hfr2)
    | (refine ⟨hx29, ?_, ?_, ?_⟩
       · intro v hv
         exfalso
         exact hbr (hOK v hv).1
       · intro e he
         have hlt := parseHex_error_lt _ _ _ he
         obtain ⟨a, b⟩ := hE e he
         rw [(hEE e hlt).1] at a
         rw [(hEE e hlt).2] at b
         exact ⟨a, b⟩
       · exact frame_comp s.mem _ we s'.mem rt (BitVec.toNat s.sp) (BitVec.toNat wa) (BitVec.toNat wa) hb hin hA hfr hfr2)


/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

Same pattern as `FromBig`: a two-instruction allocator placed at `runtime.newobject` (`MOVZ X0, #1, LSL #16; RET`) returns the
start of a 64 KiB zeroed heap; `H` says the argument is a type descriptor of at most 32 KiB inside `rt`; `hnew` is proved by
running that code; `s0` is a concrete call of `FromHex` on the string `"0x1f"` satisfying the whole precondition. -/
namespace Witness

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hnew : NewobjectContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, typ, hargs, hin, hsz, hacc, hz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun hpos => ?_⟩
  · simp only [retStateX]; rw [callRegs_eq]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
    have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
      (typNoscan s.mem (s.regs 0).toNat) hsz
    have hle : typSize s.mem (s.regs 0).toNat ≤
        blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat) := by
      unfold blockSize; split
      · exact Nat.le_refl _
      · exact le_roundupsize _ _
    simp only [maxSmallSize] at hb
    have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
    rw [hheap]
    refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
      by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
    · rw [rtView_accessible] at hacc
      exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
      exact fun i hi => this i (by omega)

/-- the string `"0x1f"` at `0x30800`, and non-nil package error variables at `1792784 + 16 k` -/
def wEntries : List (Nat × Nat) :=
  [(0x30800, 0x30), (0x30801, 0x78), (0x30802, 0x31), (0x30803, 0x66),
   (1792784, 1), (1792800, 1), (1792816, 1), (1792832, 1), (1792848, 1), (1792864, 1)]

theorem wEntries_none (a : Nat) (h : a < 0x20000) : wEntries.lookup a = none := by
  unfold wEntries
  have h1 : (a == 0x30800) = false := by simp; omega
  have h2 : (a == 0x30801) = false := by simp; omega
  have h3 : (a == 0x30802) = false := by simp; omega
  have h4 : (a == 0x30803) = false := by simp; omega
  have h5 : (a == 1792784) = false := by simp; omega
  have h6 : (a == 1792800) = false := by simp; omega
  have h7 : (a == 1792816) = false := by simp; omega
  have h8 : (a == 1792832) = false := by simp; omega
  have h9 : (a == 1792848) = false := by simp; omega
  have h10 : (a == 1792864) = false := by simp; omega
  simp [List.lookup, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((wEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def hpp : BitVec 64 := BitVec.ofNat 64 0x30800

def s0 : State :=
  { regs := fun i => if i = 0 then hpp else if i = 1 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 4, false⟩,
      ⟨1792784, 96, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [hpp, 4] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide, by decide, ?_⟩
  intro i hi
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      have := hbase d hd
      have hh : heap + i < 0x20000 := by simp only [heap]; omega
      simp only [decide_eq_true_eq]
      omega
    simp only [bytes, h1]
    have h2 : wEntries.lookup (heap + i) = none := wEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 48 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧ s0.regs 29 = s0.sp - 8#64 ∧
    H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) ∧
    Ptr s0.mem hpp (4 : BitVec 64).toNat false ∧ Outside hpp.toNat (4 : BitVec 64).toNat rt ∧
    Disjoint hpp.toNat (4 : BitVec 64).toNat (s0.sp.toNat - 4144) 4168 ∧
    s0.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s0.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
    Outside errBase 96 rt ∧ Disjoint errBase 96 (s0.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
    Outside ((s0.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4144) 4168 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, rfl, hH, ⟨by decide, by decide⟩, ?_, ?_, by decide, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · unfold Disjoint; decide
  · intro e he
    obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    all_goals decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · unfold Disjoint; decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · unfold Disjoint; decide

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/FromHex.lean
def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = the frame
of the caller (the argument of `H` in `hH`), `X28`/memory as in `s0`. -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite H rt 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 48 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [hp, len] s ∧
    (GuardOK s 48 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        Ptr s.mem hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
        Disjoint hp.toNat len.toNat (s.sp.toNat - 4144) 4168 ∧
        s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Outside errBase 96 rt ∧ Disjoint errBase 96 (s.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
        Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 2 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, hpp, 4, ret, s0, hnew, hret, setup, pre,
    ⟨wsNew, rfl, wsNew_pre⟩,
    correctness impl rt H hpp 4 hnew ret hret s0 setup pre⟩
end Witness

end Fv256.Arm64.FromHex
