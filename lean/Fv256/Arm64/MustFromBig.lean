import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC
import Fv256.Arm64.MustFromBigSfb

/-!
# `uint256.MustFromBig(b *big.Int) (*Int, bool)` (arm64)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.MustFromBig

/-- the type descriptor and data pointer `MustFromBig` passes to `runtime.gopanic` for `panic("overflow")`, recomputed from the extracted words. -/
def panicType : Nat := Extracted.dataAddr.«type:string#f88732b8»

def panicData : Nat := Extracted.dataAddr.«.rodata#ee30ac37»

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x30) (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 12)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromBig" 13) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (P : PanicRuntime) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168))
      (fun _ => goClass P)
      (fun s s' => (x.toNat = 0 ∨ len.toNat ≤ 4) ∧
        (x.toNat = 0 → s'.regs 0 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])))
      (fun s v _ => x.toNat ≠ 0 ∧ 4 < len.toNat ∧ v = ⟨panicType, panicData⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hfp, hH, hxx⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_eval_nat hpt : panicType
  janus_eval_nat hpd : panicData
  janus_data hd [hw]
  refine GoReturns.of_reaches ?_
  janus_run until [Extracted.entry + 0x3c] calls [hnew.pos]
  · exact ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), fun h => h.elim⟩
  · obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9⟩ := hxx hbr
    simp only [Disjoint] at hx8 hx9
    obtain ⟨hxa, hxb⟩ := hx1
    obtain ⟨hpa, hpb⟩ := hx5
    have hdx := InRanges.disjoint ‹InRanges _ 32 rt› hx6
    have hdp := InRanges.disjoint ‹InRanges _ 32 rt› hx7
    have hds := InRanges.disjoint ‹InRanges _ 32 rt› hout
    janus_run calls [Fv256.Arm64.MustFromBigSfb.sfb_summary impl pw len]
    · rename_i g hxn wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cflag cval cfr
      have hov := Fv256.C.flag_false _ _ cflag hbr
      have h4 := Fv256.C.ovT _ hov
      refine ⟨⟨panicType, panicData⟩, ?_, h4, ?_⟩
      · show (⟨panicType, panicData⟩ : Eface) = ⟨_, _⟩
        simp [setReg, panicType, panicData]
        exact ⟨by decide, by decide⟩
      · rw [hpt, hpd]
    · rename_i g wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cflag cval cfr
      have hov := Fv256.C.flag_true _ _ cflag hbr
      have hle4 := Fv256.C.ovF_of _ hov
      refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), hle4, fun h => h.elim, _, rfl, hin, h16, hacc, ?_, ?_⟩
      · rw [Fv256.C.bigAbs_write, Fv256.C.bigAbs_frame _ _ _ _ _ hfr, Fv256.C.bigAbs_write, Fv256.C.bigAbs_write,
          Fv256.C.bigAbs_write] at cval
        · exact cval
        all_goals first
          | omega
          | (simp only [outside_append, outside_cons, outside_nil, and_true]
             exact ⟨hx7, by omega, by omega⟩)
      · janus_frame

/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

Same pattern as Janus' `audit/round9/controls/NewPair_witness.lean`: a two-instruction allocator placed at
`runtime.newobject` (`MOVZ X0, #1, LSL #16; RET`) returns the start of a 64 KiB zeroed heap; `H` says the argument is a type
descriptor of at most 32 KiB inside `rt`; `hnew` is proved by running that code; `s0` is a concrete call of `FromBig`
on the big.Int `-(5 + 2^64)` satisfying the whole precondition. `fires` applies `correctness` to it. -/
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

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((Fv256.C.bigEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def xp : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then xp else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [xp] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide,
    by decide, ?_⟩
  intro i hi
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
    have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      have := hbase d hd
      have hh : heap + i < 0x20000 := by simp only [heap]; omega
      simp only [decide_eq_true_eq]
      omega
    simp only [bytes, h1]
    have h2 : Fv256.C.bigEntries.lookup (heap + i) = none := Fv256.C.bigEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 0 ∧ StackOK s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4144) 4168 rt ∧ s0.regs 29 = s0.sp - 8#64 ∧
    H [intType] (s0.regs 28).toNat (s0.sp.toNat - 48) (rtView rt s0.mem) ∧
    (xp.toNat ≠ 0 → Ptr s0.mem xp 32 false ∧ s0.mem.readLE xp.toNat 1 < 2 ∧
      s0.mem.readLE (xp.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (xp.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Ptr s0.mem pw (8 * (2 : BitVec 64).toNat) false ∧ Outside xp.toNat 32 rt ∧ Outside pw.toNat (8 * (2 : BitVec 64).toNat) rt ∧
      Disjoint xp.toNat 32 (s0.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * (2 : BitVec 64).toNat) (s0.sp.toNat - 4144) 4168) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, rfl, hH, fun _ => ?_⟩
  refine ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · unfold Disjoint; decide
  · unfold Disjoint; decide

/-- pins the type of an existential variable of `nonvacuous` -/
def pinPanicRuntime (_k : PanicRuntime) : Prop := True

/-- pins the type of an existential variable of `nonvacuous` -/
def pinBitVec64 (_k : BitVec 64) : Prop := True

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/MustFromBig.lean
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
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (P : PanicRuntime) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧
    (pinPanicRuntime P ∧
    pinBitVec64 pw ∧
    pinBitVec64 len ∧
    GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168)) ∧
    Go(∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ (x.toNat = 0 ∨ len.toNat ≤ 4) ∧
        (x.toNat = 0 → s'.regs 0 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))
      | .panicked v s' => x.toNat ≠ 0 ∧ 4 < len.toNat ∧ v = ⟨panicType, panicData⟩
      | .goexited _ => False := by
  refine ⟨impl, rt, H, xp, (Janus.Contracts.PanicModel.P0 [] 0), pw, 2, ret, s0, hnew, hret, setup, ?w3,
    ⟨wsNew, rfl, wsNew_pre⟩,
    correctness (Janus.Contracts.PanicModel.P0 [] 0) impl rt H xp pw 2 hnew ret hret s0 setup (?w3).2.2.2⟩
  case w3 => exact ⟨trivial, trivial, trivial, pre⟩
end Witness

end Fv256.Arm64.MustFromBig
