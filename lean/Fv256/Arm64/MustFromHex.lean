import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.SetFromHexLoops
import Fv256.Arm64.FromHexCommon

/-!
# `uint256.MustFromHex(hex string) *Int` (arm64)

`var z Int` escapes, so the compiled code calls `runtime.newobject` (pinned `NewobjectContract`) and then the non-inlined
`fromHex` (callee summary `SetFromHexLoops.fromHex_sum`, specification `Fv256.C.parseHex`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.Panic Fv256.C Fv256.Arm64.SetFromHexLoops Fv256.Arm64.FromHexCommon

namespace Fv256.Arm64.MustFromHex

/-- the type descriptor `FromHex` passes to `runtime.newobject` (`uint256.Int`), recomputed from the extracted words. -/
def intType : Nat :=
  adrpLdTarget (Extracted.entry + 0x20) (segWord Extracted.program "github.com/holiman/uint256.MustFromHex" 8)
    (segWord Extracted.program "github.com/holiman/uint256.MustFromHex" 9) 0

/-- `fromHex_sum` for an allocated receiver: `z` is whatever `X0` holds at the call; the postcondition is written out
(a callee summary's postcondition must be an explicit conjunction for the symbolic executor to unpack it). -/
theorem fromHex_summary (impl : List Segment) (hp len : BitVec 64) :
    Summary (Extracted.program.link impl) fh (fun s => FromHexPre (s.regs 0) hp len s)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24),
          (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem (s.regs 0).toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) :=
  fun s hpc hpre => fromHex_sum impl (s.regs 0) hp len s hpc hpre

set_option maxRecDepth 10000 in
theorem frame_comp (m c w m' : Memory) (rt : List (Nat × Nat)) (sp wa v : Nat) (hsp : 4144 ≤ sp)
    (hin : InRanges wa 32 rt) (hA : MemFrame m c [(sp - 4144, sp + 24)])
    (hfr : MemFrame c w (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr2 : MemFrame (w.writeLE (sp - 16) 8 v) m'
      [(wa, wa + 32), (sp - 48 + 16, sp - 48 + 24), (sp - 48 - 24, sp - 48 - 8)]) :
    MemFrame m m' (rt ++ [(sp - 4144, sp + 24)]) := by
  have hB : MemFrame m w (rt ++ [(sp - 4144, sp + 24)]) := by
    refine hA.trans hfr ?_
    intro a n h
    rw [outside_append] at h
    obtain ⟨h1, h2⟩ := h
    simp only [outside_cons, outside_nil] at h2
    refine ⟨?_, ?_⟩
    · simp only [outside_cons, outside_nil]; exact ⟨h2.1, trivial⟩
    · rw [outside_append]
      refine ⟨h1, ?_⟩
      simp only [outside_cons, outside_nil]
      obtain ⟨h3, -⟩ := h2
      refine ⟨?_, ?_, trivial⟩ <;> omega
  have hC : MemFrame m (w.writeLE (sp - 16) 8 v) (rt ++ [(sp - 4144, sp + 24)]) :=
    hB.writeLE v (r := (sp - 4144, sp + 24)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
  refine hC.trans hfr2 ?_
  intro a n h
  refine ⟨h, ?_⟩
  rw [outside_append] at h
  obtain ⟨h1, h2⟩ := h
  simp only [outside_cons, outside_nil] at h2 ⊢
  have h3 := InRanges.disjoint hin h1
  obtain ⟨h4, -⟩ := h2
  refine ⟨?_, ?_, ?_, trivial⟩ <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (P : PanicRuntime) (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [hp, len]
      (fun s => GuardOK s 48 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ s.regs 29 = s.sp - 8#64 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem) ∧
        Ptr s.mem hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
        Disjoint hp.toNat len.toNat (s.sp.toNat - 4144) 4168 ∧
        s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Outside errBase 96 rt ∧ Disjoint errBase 96 (s.sp.toNat - 4144) 4168 ∧ Outside tabBase 256 rt ∧
        Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168 ∧
        (∀ e, e < 6 → s.mem.accessible (s.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
          Outside (s.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
          Disjoint (s.mem.readLE (errAddrOf e) 8 + 8) 8 (s.sp.toNat - 4144) 4168))
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v) ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ val256 s'.mem ptr = v) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)]))
      (fun s v _ => ∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e ∧
        v = ⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, hfp, hH, ⟨hps, hps'⟩, hout1, hd1, herr, hnn, hout2, hd2, hout3, hout4, hd4, hitab⟩
  simp only [errBase_val, tabBase_val] at *
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hd1 hd2 hd4
  refine GoReturns.of_reaches ?_
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
  janus_run until [Extracted.entry + 0x50] calls [fromHex_summary impl hp len]
  all_goals
    rename_i hguard hpcA hpcB hsp h28 h29 h30 h18 hE hfr2 hOK
    rw [hB] at hE hOK
    first
    | (refine ⟨hx29, ?_, ?_, ?_⟩
       · cases hpar : parseHex (bytesAt s.mem hp.toNat) len.toNat with
         | ok v => exact ⟨v, rfl⟩
         | error e =>
           exfalso
           have hlt := parseHex_error_lt _ _ _ hpar
           have h0 := (hE e hpar).1
           rw [(hEE e hlt).1] at h0
           have h00 : s'.regs 0 = 0 := BitVec.eq_of_toNat_eq (by simpa using hbr)
           rw [h00] at h0
           exact hnz e hlt h0.symm
       · intro v hv
         obtain ⟨a, b, c⟩ := hOK v hv
         exact ⟨BitVec.toNat wa, rfl, hin, h16, hacc, c⟩
       · exact frame_comp s.mem _ we s'.mem rt (BitVec.toNat s.sp) (BitVec.toNat wa) (BitVec.toNat wa) hb hin hA hfr hfr2)
    | (obtain ⟨e, hpe⟩ : ∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = Except.error e := by
         cases hpar : parseHex (bytesAt s.mem hp.toNat) len.toNat with
         | error e => exact ⟨e, rfl⟩
         | ok v => exact absurd (hOK v hpar).1 (by simpa using hbr)
       have he6 := parseHex_error_lt _ _ _ hpe
       have hreg := (hE e hpe).1
       rw [(hEE e he6).1] at hreg
       have hip : BitVec.toNat (s'.regs 0) = s.mem.readLE (errAddrOf e) 8 := by
         rw [hreg, BitVec.toNat_ofNat]
         have h1 := Memory.readLE_lt s.mem (errAddrOf e) 8
         have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
         rw [h8] at h1
         exact Nat.mod_eq_of_lt h1
       obtain ⟨hia, hio, hid⟩ := hitab e he6
       have hbnd := Memory.accessible_bound _ hia
       have hacc' : s'.mem.accessible (BitVec.toNat (s'.regs 0) + 8) 8 false = true := by
         rw [hfr2.accessible]
         simp only [Memory.accessible_writeLE]
         rw [hfr.accessible]
         simp only [Memory.accessible_writeLE]
         rw [hip]; exact hia
       have hlt : BitVec.toNat (s'.regs 0) + 8 < 2 ^ 64 := by rw [hip]; omega
       simp only [Disjoint] at hid
       have e5 := InRanges.disjoint hin hio
       have hv : s'.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8 = s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8 := by
         rw [hfr2.readLE _ _ (by
           simp only [outside_cons, outside_nil]
           refine ⟨?_, ?_, ?_, trivial⟩ <;> omega)]
         rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
         rw [hfr.readLE _ _ (by
           rw [outside_append]
           refine ⟨hio, ?_⟩
           simp only [outside_cons, outside_nil]
           refine ⟨?_, ?_, trivial⟩ <;> omega)]
         simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint]
       have hreg1 := (hE e hpe).2
       rw [(hEE e he6).2] at hreg1
       janus_run
       refine ⟨⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩, ?_, e, hpe, rfl⟩
       show (⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩ : Eface) =
         ⟨(setReg (setReg s'.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8))) 30 745112#64 0).toNat,
          (setReg (setReg s'.regs 0 (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8))) 30 745112#64 1).toNat⟩
       simp only [setReg_apply]
       have rl : ∀ (m : Memory) (a : Nat), (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
         intro m a
         rw [BitVec.toNat_ofNat]
         have h1 := Memory.readLE_lt m a 8
         have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
         rw [h8] at h1
         exact Nat.mod_eq_of_lt h1
       simp [hreg1, rl])


/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

Same pattern as `FromBig`: a two-instruction allocator placed at `runtime.newobject` (`MOVZ X0, #1, LSL #16; RET`) returns the
start of a 64 KiB zeroed heap; `H` says the argument is a type descriptor of at most 32 KiB inside `rt`; `hnew` is proved by
running that code; `s0` is a concrete call of `MustFromHex` on the string `"0x1f"` satisfying the whole precondition. -/
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

/-- the string `"0x1f"` at `0x30800`; the package error variables at `1792784 + 16 k` hold the itab pointer `0x30900 + 16 k`
(little-endian bytes), the itabs being readable -/
def wEntries : List (Nat × Nat) :=
  [(0x30800, 0x30), (0x30801, 0x78), (0x30802, 0x31), (0x30803, 0x66),
   (1792784, 0x00), (1792785, 0x09), (1792786, 0x03), (1792800, 0x10), (1792801, 0x09), (1792802, 0x03),
   (1792816, 0x20), (1792817, 0x09), (1792818, 0x03), (1792832, 0x30), (1792833, 0x09), (1792834, 0x03),
   (1792848, 0x40), (1792849, 0x09), (1792850, 0x03), (1792864, 0x50), (1792865, 0x09), (1792866, 0x03)]

theorem wEntries_none (a : Nat) (h : a < 0x20000) : wEntries.lookup a = none := by
  unfold wEntries
  have h0 : (a == 198656) = false := by simp; omega
  have h1 : (a == 198657) = false := by simp; omega
  have h2 : (a == 198658) = false := by simp; omega
  have h3 : (a == 198659) = false := by simp; omega
  have h4 : (a == 1792784) = false := by simp; omega
  have h5 : (a == 1792785) = false := by simp; omega
  have h6 : (a == 1792786) = false := by simp; omega
  have h7 : (a == 1792800) = false := by simp; omega
  have h8 : (a == 1792801) = false := by simp; omega
  have h9 : (a == 1792802) = false := by simp; omega
  have h10 : (a == 1792816) = false := by simp; omega
  have h11 : (a == 1792817) = false := by simp; omega
  have h12 : (a == 1792818) = false := by simp; omega
  have h13 : (a == 1792832) = false := by simp; omega
  have h14 : (a == 1792833) = false := by simp; omega
  have h15 : (a == 1792834) = false := by simp; omega
  have h16 : (a == 1792848) = false := by simp; omega
  have h17 : (a == 1792849) = false := by simp; omega
  have h18 : (a == 1792850) = false := by simp; omega
  have h19 : (a == 1792864) = false := by simp; omega
  have h20 : (a == 1792865) = false := by simp; omega
  have h21 : (a == 1792866) = false := by simp; omega
  simp [List.lookup, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

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
      ⟨1792784, 96, false⟩, ⟨0x30900, 0x100, false⟩] ++ dregs⟩ }

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
    Outside ((s0.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4144) 4168 ∧
    (∀ e, e < 6 → s0.mem.accessible (s0.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
      Outside (s0.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
      Disjoint (s0.mem.readLE (errAddrOf e) 8 + 8) 8 (s0.sp.toNat - 4144) 4168) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, rfl, hH, ⟨by decide, by decide⟩, ?_, ?_, by decide, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro e he
    obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    all_goals (refine ⟨by decide, ?_, ?_⟩; (simp only [rt, outside_cons, outside_nil]; decide); (unfold Disjoint; decide))

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
        Outside ((s.regs 28).toNat + 16) 8 rt ∧ Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168 ∧
        (∀ e, e < 6 → s.mem.accessible (s.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
          Outside (s.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
          Disjoint (s.mem.readLE (errAddrOf e) 8 + 8) 8 (s.sp.toNat - 4144) 4168)) :=
  ⟨impl, rt, H, hpp, 4, ret, s0, hnew, hret, setup, pre⟩

end Witness

end Fv256.Arm64.MustFromHex
