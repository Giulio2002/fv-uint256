import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC
import Fv256.Arm64.FromBigSfb

/-!
# `uint256.FromBig(b *big.Int) (*Int, bool)` (arm64)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.FromBig

def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.FromBig" 8)
    (segWord Extracted.program "github.com/holiman/uint256.FromBig" 9) 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168))
      (fun s s' => (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 1 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          (s'.regs 1).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hfp, hH, hxx⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x2c] calls [hnew.pos]
  · exact ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), fun h => h.elim⟩
  · obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9⟩ := hxx hbr
    simp only [Disjoint] at hx8 hx9
    obtain ⟨hxa, hxb⟩ := hx1
    obtain ⟨hpa, hpb⟩ := hx5
    have hdx := InRanges.disjoint ‹InRanges _ 32 rt› hx6
    have hdp := InRanges.disjoint ‹InRanges _ 32 rt› hx7
    have hds := InRanges.disjoint ‹InRanges _ 32 rt› hout
    janus_run calls [Fv256.Arm64.FromBigSfb.sfb_summary impl pw len]
    rename_i wa wb wc wd we wf wg hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cflag cval cfr
    refine ⟨Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb), fun h => h.elim, _, rfl, hin, h16, hacc, ?_, cflag, ?_⟩
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
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length

def bytes (a : Nat) : Byte :=
  if tyA ≤ a ∧ a < tyA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0)
  else BitVec.ofNat 8 ((Fv256.C.bigEntries.lookup a).getD 0)

def xp : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then xp else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4144, 4168, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩, ⟨0x30800, 0x100, false⟩]⟩ }

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
  have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + dlen) := by
    simp only [tyA, heap, dlen]; omega
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · simp only [bytes]; rw [if_neg h1]
    have h2 : Fv256.C.bigEntries.lookup (heap + i) = none := Fv256.C.bigEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

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
def pinBitVec64 (_k : BitVec 64) : Prop := True

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/FromBig.lean
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
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (x : BitVec 64) (pw : BitVec 64) (len : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [x] s ∧
    (pinBitVec64 pw ∧
    pinBitVec64 len ∧
    GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Ptr s.mem pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          Disjoint x.toNat 32 (s.sp.toNat - 4144) 4168 ∧ Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 4144) 4168)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 1 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          val256 s'.mem ptr = Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          (s'.regs 1).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  refine ⟨impl, rt, H, xp, pw, 2, ret, s0, hnew, hret, setup, ?w3,
    ⟨wsNew, rfl, wsNew_pre⟩,
    correctness impl rt H xp pw 2 hnew ret hret s0 setup ?w3⟩
  case w3 => exact ⟨trivial, trivial, pre⟩
end Witness

end Fv256.Arm64.FromBig
