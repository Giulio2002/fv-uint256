import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.UtilH
import Fv256.Arm64.DivMod
import Fv256.Arm64.DivMSlots

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Arm64.DivMod

namespace Fv256.Arm64.DivModMain

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m]
      (fun s => GuardOK s 464 ∧ StackOK s 4256 40 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4256) (4256 + 40) rt ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m true ∧
        Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint x.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
        Disjoint y.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint m.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
        (z = m ∨ Disjoint32 z.toNat m.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
        Outside ((s.regs 28).toNat + 16) 8 rt ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 160) (rtView rt s.mem))
      (fun s s' => s'.regs 0 = z ∧
        ∃ m' : Nat, (s'.regs 1).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
          (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
          val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          val256 s'.mem m' = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
            (s.sp.toNat - 4256, s.sp.toNat + 40)])) := by
  intro ret hret s hs ⟨hg, ⟨hal, hb, ha, hw⟩, hd, hout, hzp, hxp, hyp, hmp, hzo, hxo, hyo, hmo, hdz, hdx, hdy, hdm, hzm, hdg, hgo, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  obtain ⟨⟨hzb, hza⟩, ⟨hxb, hxa⟩, ⟨hyb, hya⟩, ⟨hmb, hma⟩⟩ := And.intro hzp (And.intro hxp (And.intro hyp hmp))
  simp only [Disjoint] at hdz hdx hdy hdm
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hout := hout
  janus_run until [Extracted.entry + 0x40, Extracted.entry + 0x64] calls [hnew.pos]
  · -- alloc
    rename_i ptrW rr fl vr mmm ex exp cfr cin clt cacc cal8 cal16 czb ctriv
    have hdj := InRanges.disjoint cin hout
    have hdzp := InRanges.disjoint cin hzo
    have hdxp := InRanges.disjoint cin hxo
    have hdyp := InRanges.disjoint cin hyo
    have hmz : m = z := BitVec.eq_of_toNat_eq (by omega)
    janus_run until [Extracted.entry + 0x64]
    have hsp160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; omega
    have hptr : BitVec.ofNat 64 ptrW.toNat = ptrW := by simp
    apply Fv256.H.reaches_return_mono (P := fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ ∃ m'', (s'.regs 1).toNat = m'' ∧ m'' = ptrW.toNat ∧ val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧ val256 s'.mem m'' = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧ MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (ptrW.toNat, ptrW.toNat + 32), (s.sp.toNat - 4256, s.sp.toNat + 40)]))
    case hq =>
      intro S ⟨c1, c2, m'', c3, c4, c5, c6, c7⟩
      subst c4
      refine ⟨c1, c2, ptrW.toNat, c3, fun h => absurd hmz.symm h, fun _ => ⟨cin, cal16, ?_⟩, c5, c6, ?_⟩
      · rw [c7.accessible]; exact cacc
      · refine c7.mono ?_
        intro a n h
        simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true] at h ⊢
        have hd := InRanges.disjoint cin h.1
        exact ⟨h.1, h.2.1, hd, h.2.2.2⟩
    case h =>
      have hs := Fv256.Arm64.DivMSlots.alloc_slots rt s.mem mmm s.sp.toNat ret (s.regs 29).toNat z.toNat x.toNat y.toNat ptrW.toNat
        (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8) (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) hb hout (by omega) cfr
      have a1 : ptrW.toNat + 32 ≤ 2 ^ 48 := by omega
      have a2 : z.toNat + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ z.toNat := by omega
      have a3 : x.toNat + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ x.toNat := by omega
      have a4 : y.toNat + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ y.toNat := by omega
      have a5 : ptrW.toNat + 32 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ ptrW.toNat := by omega
      have a6 : z.toNat + 32 ≤ ptrW.toNat ∨ ptrW.toNat + 32 ≤ z.toNat := by omega
      refine partB impl rt z x y m ptrW.toNat ret hret s _ hal hb ha hw hout hzb hza hxb hxa hyb hya cacc a1
        hxo hyo hzo a2 a3 a4 a5 a6 hg1 hg2 hg3 hdg hgo (Or.inl cin) ?a_hpc hsp160 ?a_h0 ?a_h1 ?a_h2 ?a_h3 ?a_h18 ?a_h28 ?a_h29 ?a_hfr ?a_hretslot ?a_hbp ?a_hz8
        ?a_hr30 ?a_hr30b h_lr
      case a_hpc => simp only [dm, reduceSegAddr, Nat.reduceAdd]
      case a_h0 => simp [setReg_apply]
      case a_h1 => simp [setReg_apply]
      case a_h2 => simp [setReg_apply]
      case a_h3 => simp [setReg_apply]
      case a_h18 => simp [setReg_apply, callRegs]
      case a_h28 => simp [setReg_apply, callRegs]
      case a_h29 => simp [setReg_apply, callRegs]
      case a_hfr => janus_frame
      case a_hretslot =>
        simp only [hsp160]
        rw [hs.1]; exact RetAddr.mod64 hret
      case a_hbp =>
        simp only [hsp160]
        rw [hs.2.1]; exact Nat.mod_eq_of_lt (by simpa using (s.regs 29).isLt)
      case a_hz8 =>
        simp only [hsp160]
        rw [hs.2.2]; exact Nat.mod_eq_of_lt (by simpa using z.isLt)
      case a_hr30 => rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
      case a_hr30b => rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega
  · -- no allocation: z != m
    have hne : z.toNat ≠ m.toNat := by omega
    have hzm2 : z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat := by
      rcases hzm with h | h
      · exact absurd (congrArg BitVec.toNat h) (by omega)
      · simp only [Disjoint32, Disjoint] at h; exact h
    have hsp160 : (s.sp - 160#64).toNat = s.sp.toNat - 160 := by
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; have := s.sp.isLt; omega
    apply Fv256.H.reaches_return_mono (P := fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧ ∃ m'', (s'.regs 1).toNat = m'' ∧ m'' = m.toNat ∧ val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧ val256 s'.mem m'' = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧ MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), (s.sp.toNat - 4256, s.sp.toNat + 40)]))
    case hq =>
      intro S ⟨c1, c2, m'', c3, c4, c5, c6, c7⟩
      subst c4
      refine ⟨c1, c2, m.toNat, c3, fun _ => rfl, fun h => absurd (by rw [h]) hne, c5, c6, c7⟩
    case h =>
      refine partB impl rt z x y m m.toNat ret hret s _ hal hb ha hw hout hzb hza hxb hxa hyb hya hmb hma
        hxo hyo hzo (by omega) (by omega) (by omega) (by omega) hzm2 hg1 hg2 hg3 hdg hgo (Or.inr rfl) ?hpc hsp160 ?h0 ?h1 ?h2 ?h3 ?h18 ?h28 ?h29 ?hfr ?hretslot ?hbp ?hz8
        ?hr30 ?hr30b h_lr
      case hpc => simp only [dm, reduceSegAddr, Nat.reduceAdd]
      case h0 => simp [setReg_apply, h_x0]
      case h1 => simp [setReg_apply, h_x1]
      case h2 => simp [setReg_apply, h_x2]
      case h3 => simp [setReg_apply, h_x3]
      case h18 => simp [setReg_apply]
      case h28 => simp [setReg_apply]
      case h29 => simp [setReg_apply]
      case hfr => janus_frame
      case hretslot =>
        simp (disch := omega) only [hsp160, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
        exact RetAddr.mod64 hret
      case hbp =>
        have hh := (Fv256.Arm64.DivMSlots.slots s.mem s.sp.toNat ret (s.regs 29).toNat z.toNat (by omega)).1
        simp only [hsp160]
        rw [hh]; exact Nat.mod_eq_of_lt (by simpa using (s.regs 29).isLt)
      case hz8 =>
        have hh := (Fv256.Arm64.DivMSlots.slots s.mem s.sp.toNat ret (s.regs 29).toNat z.toNat (by omega)).2
        simp only [hsp160]
        rw [hh]; exact Nat.mod_eq_of_lt (by simpa using z.isLt)
      case hr30 => rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; have := hret.aligned; omega
      case hr30b => rw [h_lr, BitVec.toNat_ofNat]; have := hret.user; omega


namespace Witness

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rtW : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- A toy allocator at the runtime.newobject address: `MOVZ X0, #1, LSL #16; RET` (returns the heap at `0x10000`). -/
def implW : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def HW : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rtW ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link implW

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hnewW : NewobjectContract (Extracted.program.link implW)
    (Extracted.program.contractAddr "runtime.newobject") rtW 4096 HW := by
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
    refine ⟨⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, by simp only [heap]; omega⟩,
      by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
    · rw [rtView_accessible] at hacc
      exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩
      exact fun i hi => this i (by omega)

def retW : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def xp : Nat := 0x30900
def yp : Nat := 0x30a00
def mp : Nat := 0x30b00
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length

def bytesW (a : Nat) : Byte :=
  if tyA ≤ a ∧ a < tyA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0) else 0

def zW : BitVec 64 := BitVec.ofNat 64 zp
def xW : BitVec 64 := BitVec.ofNat 64 xp
def yW : BitVec 64 := BitVec.ofNat 64 yp
def mW : BitVec 64 := BitVec.ofNat 64 mp

def s0 : State :=
  { regs := fun i => if i = 0 then zW else if i = 1 then xW else if i = 2 then yW else if i = 3 then mW
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 29 then BitVec.ofNat 64 sp0 - 8#64
      else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytesW, [⟨sp0 - 4256, 4296, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩, ⟨zp, 32, true⟩, ⟨xp, 32, false⟩, ⟨yp, 32, false⟩, ⟨mp, 32, true⟩]⟩ }

theorem hretW : RetAddr linked retW := RetAddr.of_check (by decide)

theorem setupW : CallSetup (linked.withExit retW) Extracted.entry [zW, xW, yW, mW] s0 :=
  ⟨rfl, rfl, by
    intro r h
    match r, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoadedW : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hHW : HW [intType] (s0.regs 28).toNat (s0.sp.toNat - 160) (rtView rtW s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rtW], Nat.le_refl _, Nat.le_refl _⟩, by decide,
    by decide, ?_⟩
  intro i hi
  have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + dlen) := by
    simp only [tyA, heap, dlen]; omega
  show (if _ then bytesW (heap + i) else 0) = 0
  split
  · simp only [bytesW]; rw [if_neg h1]
  · rfl

set_option maxRecDepth 100000 in
theorem preW : GuardOK s0 464 ∧ StackOK s0 4256 40 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4256) (4256 + 40) rtW ∧
    Ptr32 s0.mem zW true ∧ Ptr32 s0.mem xW false ∧ Ptr32 s0.mem yW false ∧ Ptr32 s0.mem mW true ∧
    Outside zW.toNat 32 rtW ∧ Outside xW.toNat 32 rtW ∧ Outside yW.toNat 32 rtW ∧ Outside mW.toNat 32 rtW ∧
    Disjoint zW.toNat 32 (s0.sp.toNat - 4256) (4256 + 40) ∧ Disjoint xW.toNat 32 (s0.sp.toNat - 4256) (4256 + 40) ∧
    Disjoint yW.toNat 32 (s0.sp.toNat - 4256) (4256 + 40) ∧ Disjoint mW.toNat 32 (s0.sp.toNat - 4256) (4256 + 40) ∧
    (zW = mW ∨ Disjoint32 zW.toNat mW.toNat) ∧
    ((s0.regs 28).toNat + 24 ≤ s0.sp.toNat - 4256 ∨ s0.sp.toNat + 40 ≤ (s0.regs 28).toNat + 16) ∧
    Outside ((s0.regs 28).toNat + 16) 8 rtW ∧
    HW [intType] (s0.regs 28).toNat (s0.sp.toNat - 160) (rtView rtW s0.mem) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoadedW, ?_,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ?_, ?_, ?_, ?_, by unfold Disjoint; decide, by unfold Disjoint; decide, by unfold Disjoint; decide,
    by unfold Disjoint; decide, Or.inr (by unfold Disjoint32 Disjoint zW mW zp mp; decide), by decide, ?_, hHW⟩
  all_goals simp only [rtW, outside_cons, outside_nil]; decide

/-- Non-vacuity of `correctness`: every hypothesis (the runtime contract included) holds together for a toy allocator and a concrete call. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, x, y, m] s ∧
    (GuardOK s 464 ∧ StackOK s 4256 40 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4256) (4256 + 40) rt ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m true ∧
      Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
      Disjoint z.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint x.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
      Disjoint y.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint m.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
      (z = m ∨ Disjoint32 z.toNat m.toNat) ∧
      ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
      Outside ((s.regs 28).toNat + 16) 8 rt ∧
      H [intType] (s.regs 28).toNat (s.sp.toNat - 160) (rtView rt s.mem)) :=
  ⟨implW, rtW, HW, zW, xW, yW, mW, retW, s0, hnewW, hretW, setupW, preW⟩

end Witness

end Fv256.Arm64.DivModMain
