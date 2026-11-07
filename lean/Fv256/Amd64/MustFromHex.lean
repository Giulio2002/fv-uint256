import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.SumC64
import Fv256.Amd64.SetFromHexLoops

/-!
# `uint256.MustFromHex(hex string) *Int` (amd64)

`var z Int` escapes, so the compiled code calls `runtime.newobject` (pinned `NewobjectContract64`) and then the non-inlined
`fromHex` (callee summary `SetFromHexLoops.fromHex_sum`, specification `Fv256.C.parseHex`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64 Fv256.C Fv256.Amd64.SetFromHexLoops

namespace Fv256.Amd64.MustFromHex

def intType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 100000 in
theorem tabData : ∀ c, c < 256 → (dataRead Extracted.program (5176782 + c) 1).isSome = true ∧
    dataReadD Extracted.program (5176782 + c) 1 = (hexNib c).getD 255 := by
  decide

theorem tab_vals {m : Janus.Arm64.Memory} (h : Extracted.program.DataLoaded m) :
    ∀ c, c < 256 → m.readLE (5176782 + c) 1 = (hexNib c).getD 255 := by
  intro c hc
  obtain ⟨h1, h2⟩ := tabData c hc
  rw [readLE_dataReadD h _ _ h1, h2]

/-- `fromHex_sum` for an allocated receiver: `z` is whatever `RAX` holds at the call; the postcondition is written out. -/
theorem fromHex_summary (impl : List Janus.Amd64.Segment) (hp len : BitVec 64) :
    Summary (Extracted.program.link impl) fh (fun s => FromHexPre (s.regs 0) hp len s)
      (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
        Janus.MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
          ((s.regs 4).toNat - 8, (s.regs 4).toNat)] ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem (s.regs 0).toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) :=
  fun s hpc hpre => fromHex_sum impl (s.regs 0) hp len s hpc hpre

set_option maxRecDepth 10000 in
theorem frame_comp (m c w m' : Janus.Arm64.Memory) (rt : List (Nat × Nat)) (sp wa v v2 : Nat) (hsp : 4144 ≤ sp)
    (hin : InRanges wa 32 rt) (hA : Janus.MemFrame m c [(sp - 4144, sp + 24)])
    (hfr : Janus.MemFrame c w (rt ++ [(sp - 48 - 4096, sp - 48), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr2 : Janus.MemFrame ((w.writeLE (sp - 16) 8 v).writeLE (sp - 48) 8 v2) m'
      [(wa, wa + 32), (sp - 48 + 16, sp - 48 + 24), (sp - 48 - 8, sp - 48)]) :
    Janus.MemFrame m m' (rt ++ [(sp - 4144, sp + 24)]) := by
  have hB : Janus.MemFrame m w (rt ++ [(sp - 4144, sp + 24)]) := by
    refine hA.trans hfr ?_
    intro a n h
    rw [Janus.outside_append] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Janus.outside_cons, Janus.outside_nil] at h2
    refine ⟨?_, ?_⟩
    · simp only [Janus.outside_cons, Janus.outside_nil]; exact ⟨h2.1, trivial⟩
    · rw [Janus.outside_append]
      refine ⟨h1, ?_⟩
      simp only [Janus.outside_cons, Janus.outside_nil]
      obtain ⟨h3, -⟩ := h2
      refine ⟨?_, ?_, trivial⟩ <;> omega
  have hC : Janus.MemFrame m ((w.writeLE (sp - 16) 8 v).writeLE (sp - 48) 8 v2) (rt ++ [(sp - 4144, sp + 24)]) :=
    (hB.writeLE v (r := (sp - 4144, sp + 24)) (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE v2
      (r := (sp - 4144, sp + 24)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
  refine hC.trans hfr2 ?_
  intro a n h
  refine ⟨h, ?_⟩
  rw [Janus.outside_append] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Janus.outside_cons, Janus.outside_nil] at h2 ⊢
  have h3 := InRanges.disjoint hin h1
  obtain ⟨h4, -⟩ := h2
  refine ⟨?_, ?_, ?_, trivial⟩ <;> omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [hp, len]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4144) 4168 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 48) (rtView rt s.mem) ∧
        Buffer s hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
        (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
        s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Outside errBase 96 rt ∧ ((errBase + 96) ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ errBase) ∧
        Outside tabBase 256 rt ∧
        (∀ e, e < 6 → s.mem.accessible (s.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
          Outside (s.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
          ((s.mem.readLE (errAddrOf e) 8 + 8) + 8 ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ s.mem.readLE (errAddrOf e) 8 + 8)))
      (fun _ => goClass P)
      (fun s s' =>
        (∃ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v) ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ Janus.Spec.val256 s'.mem ptr = v) ∧
        Janus.MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)]))
      (fun s v _ => ∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e ∧
        v = ⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hout, hal, hH, ⟨hpw, hps⟩, hout1, hd1, herr, hnn, hout2, hd2, hout3, hitab⟩
  simp only [errBase_val, tabBase_val] at *
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hout hal hH hd1 hd2
  janus64_data hd [hacc]
  refine GoReturns.of_reaches ?_
  janus64_run until [Extracted.entry + 0x25] calls [hnew.pos]
  rename_i wa wb wc wd we wf wg wh hfr hin hle hacc h8 h16 hz rr
  have htb : ∀ c, c < 256 → s.mem.readLE (5176782 + c) 1 = (hexNib c).getD 255 := tab_vals hd
  have e1 := InRanges.disjoint hin hout3
  have e2 := InRanges.disjoint hin hout1
  have e3 := InRanges.disjoint hin hout
  have e4 := InRanges.disjoint hin hout2
  have f1 : ∀ c, c < 256 → ((wf.writeLE ((s.regs 4).toNat - 16) 8 (BitVec.toNat wa)).writeLE
      ((s.regs 4).toNat - 48) 8 4922873).readLE (5176782 + c) 1 = (hexNib c).getD 255 := by
    intro c hc
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hfr.readLE (5176782 + c) 1 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout3 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact htb c hc
  have f2 : ∀ e, e < 6 → ¬ ((wf.writeLE ((s.regs 4).toNat - 16) 8 (BitVec.toNat wa)).writeLE
      ((s.regs 4).toNat - 48) 8 4922873).readLE (errAddrOf e) 8 = 0 := by
    intro e he
    have hb := errAddrOf_bounds e
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hfr.readLE (errAddrOf e) 8 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hnn e he
  have hB : parseHex (bytesAt ((wf.writeLE ((s.regs 4).toNat - 16) 8 (BitVec.toNat wa)).writeLE
      ((s.regs 4).toNat - 48) 8 4922873) hp.toNat) len.toNat = parseHex (bytesAt s.mem hp.toNat) len.toNat := by
    apply parseHex_congr
    intro k hk
    unfold bytesAt
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hfr.readLE (hp.toNat + k) 1 (by
      rw [outside_append]
      refine ⟨Outside.of_sub hout1 (by omega) (by omega), ?_⟩
      simp only [outside_cons, outside_nil]
      refine ⟨?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hEE : ∀ e, e < 6 → (((wf.writeLE ((s.regs 4).toNat - 16) 8 (BitVec.toNat wa)).writeLE
      ((s.regs 4).toNat - 48) 8 4922873).readLE (errAddrOf e) 8 = s.mem.readLE (errAddrOf e) 8) ∧
      (((wf.writeLE ((s.regs 4).toNat - 16) 8 (BitVec.toNat wa)).writeLE
      ((s.regs 4).toNat - 48) 8 4922873).readLE (errAddrOf e + 8) 8 = s.mem.readLE (errAddrOf e + 8) 8) := by
    intro e he
    have hb := errAddrOf_bounds e
    constructor
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ 8 (by
        rw [outside_append]
        refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
        simp only [outside_cons, outside_nil]
        refine ⟨?_, ?_, trivial⟩ <;> omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      rw [hfr.readLE _ 8 (by
        rw [outside_append]
        refine ⟨Outside.of_sub hout2 (by omega) (by omega), ?_⟩
        simp only [outside_cons, outside_nil]
        refine ⟨?_, ?_, trivial⟩ <;> omega)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hnz : ∀ e, e < 6 → BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ≠ 0 := by
    intro e he h0
    apply hnn e he
    have h2 : (BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8)).toNat = 0 := by rw [h0]; rfl
    rw [BitVec.toNat_ofNat] at h2
    have h1 := Janus.Arm64.Memory.readLE_lt s.mem (errAddrOf e) 8
    have h8' : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    rw [h8'] at h1
    omega
  have hA : Janus.MemFrame s.mem ((((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 16) 8 len.toNat).writeLE ((s.regs 4).toNat + 8) 8 hp.toNat).writeLE
      ((s.regs 4).toNat - 48) 8 4922853) [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)] := by
    refine (((((Janus.MemFrame.refl s.mem _).writeLE _ (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24))
      (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _
      (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)) (by simp) (by dsimp only; omega)
      (by dsimp only; omega))).writeLE _ (r := ((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)) (by simp)
      (by dsimp only; omega) (by dsimp only; omega)
  janus64_run until [Extracted.entry + 0x49] calls [fromHex_summary impl hp len]
  all_goals
    rename_i hrip hr4 hr5 hr14 hx hdf' hfs hE hfr2 hOK
    rw [hB] at hE hOK
    first
    | (refine ⟨?_, ?_, ?_⟩
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
       · exact frame_comp s.mem _ wf s'.mem rt (BitVec.toNat (s.regs 4)) (BitVec.toNat wa) (BitVec.toNat wa) 4922873 hlow hin hA hfr hfr2)
    | (obtain ⟨e, hpe⟩ : ∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = Except.error e := by
         cases hpar : parseHex (bytesAt s.mem hp.toNat) len.toNat with
         | error e => exact ⟨e, rfl⟩
         | ok v => exact absurd (hOK v hpar).1 (by simpa using hbr)
       have he6 := parseHex_error_lt _ _ _ hpe
       have hreg := (hE e hpe).1
       rw [(hEE e he6).1] at hreg
       have hip : BitVec.toNat (s'.regs 0) = s.mem.readLE (errAddrOf e) 8 := by
         rw [hreg, BitVec.toNat_ofNat]
         have h1 := Janus.Arm64.Memory.readLE_lt s.mem (errAddrOf e) 8
         have h8' : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
         rw [h8'] at h1
         exact Nat.mod_eq_of_lt h1
       obtain ⟨hia, hio, hid⟩ := hitab e he6
       have hbnd := Janus.Arm64.Memory.accessible_bound _ hia
       have hacc' : s'.mem.accessible (BitVec.toNat (s'.regs 0) + 8) 8 false = true := by
         rw [hfr2.accessible]
         simp only [Janus.Arm64.Memory.accessible_writeLE]
         rw [hfr.accessible]
         simp only [Janus.Arm64.Memory.accessible_writeLE]
         rw [hip]; exact hia
       have hlt : BitVec.toNat (s'.regs 0) + 8 < 2 ^ 64 := by rw [hip]; omega
       have e5 := InRanges.disjoint hin hio
       have hv : s'.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8 = s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8 := by
         rw [hfr2.readLE _ _ (by
           simp only [Janus.outside_cons, Janus.outside_nil]
           refine ⟨?_, ?_, ?_, trivial⟩ <;> omega)]
         simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
         rw [hfr.readLE _ _ (by
           rw [outside_append]
           refine ⟨hio, ?_⟩
           simp only [outside_cons, outside_nil]
           refine ⟨?_, ?_, trivial⟩ <;> omega)]
         simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
       have hreg3 := (hE e hpe).2
       rw [(hEE e he6).2] at hreg3
       janus64_run
       refine ⟨⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩, ?_, e, hpe, rfl⟩
       rw [goClass_gopanic]
       have rl : ∀ (m : Janus.Arm64.Memory) (a : Nat), (BitVec.ofNat 64 (m.readLE a 8)).toNat = m.readLE a 8 := by
         intro m a
         rw [BitVec.toNat_ofNat]
         have h1 := Janus.Arm64.Memory.readLE_lt m a 8
         have h8' : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
         rw [h8'] at h1
         exact Nat.mod_eq_of_lt h1
       simp [setRegF_apply, hreg3, rl])


/-! ## Non-vacuity: the allocation contract and the precondition are jointly satisfiable

As Janus' `AllocSatAmd64`: `mov $0x10000, %eax; ret` placed at `runtime.newobject` returns the start of a zeroed 64 KiB heap;
`H` says the argument is a type descriptor of at most 32 KiB inside `rt` and the heap is writable and zero; `hnew` is proved by
running that code; `s0` is a concrete call of `MustFromHex` on the big.Int `the string `"0x1f"``; `fires` applies `correctness`. -/
namespace Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

def impl : List Janus.Amd64.Segment :=
  [{ name := "witness.newobject", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] }]

def H : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

def linked : Janus.Amd64.Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem hnew : NewobjectContract64 (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
    (typNoscan s.mem (s.regs 0).toNat) hsz
  simp only [maxSmallSize] at hb
  have hle := le_blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)
  have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
  rw [hheap]
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hle⟩

/-- the string `"0x1f"` at `0x30800`; the package error variables at `5995344 + 16 k` hold the itab pointer `0x30900 + 16 k`
(little-endian bytes), the itabs being readable -/
def wEntries : List (Nat × Nat) :=
  [(198656, 48), (198657, 120), (198658, 49), (198659, 102), (5995344, 0), (5995345, 9), (5995346, 3), (5995360, 16), (5995361, 9), (5995362, 3), (5995376, 32), (5995377, 9), (5995378, 3), (5995392, 48), (5995393, 9), (5995394, 3), (5995408, 64), (5995409, 9), (5995410, 3), (5995424, 80), (5995425, 9), (5995426, 3)]

theorem wEntries_none (a : Nat) (h : a < 0x20000) : wEntries.lookup a = none := by
  unfold wEntries
  have h0 : (a == 198656) = false := by simp; omega
  have h1 : (a == 198657) = false := by simp; omega
  have h2 : (a == 198658) = false := by simp; omega
  have h3 : (a == 198659) = false := by simp; omega
  have h4 : (a == 5995344) = false := by simp; omega
  have h5 : (a == 5995345) = false := by simp; omega
  have h6 : (a == 5995346) = false := by simp; omega
  have h7 : (a == 5995360) = false := by simp; omega
  have h8 : (a == 5995361) = false := by simp; omega
  have h9 : (a == 5995362) = false := by simp; omega
  have h10 : (a == 5995376) = false := by simp; omega
  have h11 : (a == 5995377) = false := by simp; omega
  have h12 : (a == 5995378) = false := by simp; omega
  have h13 : (a == 5995392) = false := by simp; omega
  have h14 : (a == 5995393) = false := by simp; omega
  have h15 : (a == 5995394) = false := by simp; omega
  have h16 : (a == 5995408) = false := by simp; omega
  have h17 : (a == 5995409) = false := by simp; omega
  have h18 : (a == 5995410) = false := by simp; omega
  have h19 : (a == 5995424) = false := by simp; omega
  have h20 : (a == 5995425) = false := by simp; omega
  have h21 : (a == 5995426) = false := by simp; omega
  simp [List.lookup, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((wEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def hpp : BitVec 64 := BitVec.ofNat 64 0x30800

def s0 : Janus.Amd64.State :=
  { regs := fun i => if i = 0 then hpp else if i = 3 then 4 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4144, 4144 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨0x30800, 4, false⟩,
      ⟨5995344, 96, false⟩, ⟨0x30900, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

set_option maxRecDepth 100000 in
theorem setup : CallSetup (linked.withExit ret) Extracted.entry [hpp, 4] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 48) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, fun i hi => ?_⟩, tyA, rfl,
    ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide⟩
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · have h1 : dsegs.find? (fun d => decide (d.base ≤ heap + i ∧ heap + i < d.base + d.bytes.length)) = none := by
      rw [List.find?_eq_none]
      intro d hd
      have := hbase d hd
      have hh : heap + i < 0x20000 := by simp only [heap]; omega
      simp only [decide_eq_true_eq]
      omega
    have h3 : heap + i ≠ sp0 + 2 := by simp only [heap, sp0]; omega
    simp only [bytes, if_neg h3, h1]
    have h2 : wEntries.lookup (heap + i) = none := wEntries_none _ (by simp only [heap]; omega)
    rw [h2]; rfl
  · rfl

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4144 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4144) 4168 rt ∧ (s0.regs 4).toNat % 8 = 0 ∧
    H [intType] (s0.regs 14).toNat ((s0.regs 4).toNat - 48) (rtView rt s0.mem) ∧
    Buffer s0 hpp (4 : BitVec 64).toNat false ∧ Outside hpp.toNat (4 : BitVec 64).toNat rt ∧
    (hpp.toNat + (4 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 4144 ∨ (s0.regs 4).toNat + 24 ≤ hpp.toNat) ∧
    s0.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s0.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
    Outside errBase 96 rt ∧ ((errBase + 96) ≤ (s0.regs 4).toNat - 4144 ∨ (s0.regs 4).toNat + 24 ≤ errBase) ∧
    Outside tabBase 256 rt ∧
    (∀ e, e < 6 → s0.mem.accessible (s0.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
      Outside (s0.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
      ((s0.mem.readLE (errAddrOf e) 8 + 8) + 8 ≤ (s0.regs 4).toNat - 4144 ∨ (s0.regs 4).toNat + 24 ≤ s0.mem.readLE (errAddrOf e) 8 + 8)) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, by decide, hH, ⟨by decide, by decide⟩, ?_, by decide,
    by decide, ?_, ?_, by decide, ?_, ?_⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · intro e he
    obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    all_goals decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · simp only [rt, outside_cons, outside_nil]; decide
  · intro e he
    obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    all_goals (refine ⟨by decide, ?_, by decide⟩; (simp only [rt, outside_cons, outside_nil]; decide))

/-- pins the type of an existential variable of `nonvacuous` -/
def pinJanusSpecPanicRuntime (_k : Janus.Spec.PanicRuntime) : Prop := True

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `rt`, `H`), the contract hypotheses, an admissible
return address, a call state and the precondition. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (hp len : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [hp, len] s ∧
    (pinJanusSpecPanicRuntime P ∧
    StackGuardOK s 0 ∧ StackWritable s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4144) 4168 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 48) (rtView rt s.mem) ∧
        Buffer s hp len.toNat false ∧ Outside hp.toNat len.toNat rt ∧
        (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
        s.mem.accessible errBase 96 false = true ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Outside errBase 96 rt ∧ ((errBase + 96) ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ errBase) ∧
        Outside tabBase 256 rt ∧
        (∀ e, e < 6 → s.mem.accessible (s.mem.readLE (errAddrOf e) 8 + 8) 8 false = true ∧
          Outside (s.mem.readLE (errAddrOf e) 8 + 8) 8 rt ∧
          ((s.mem.readLE (errAddrOf e) 8 + 8) + 8 ≤ (s.regs 4).toNat - 4144 ∨ (s.regs 4).toNat + 24 ≤ s.mem.readLE (errAddrOf e) 8 + 8))) ∧
    GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ (∃ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v) ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
            s'.mem.accessible ptr 32 true = true ∧ Janus.Spec.val256 s'.mem ptr = v) ∧
        Janus.MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4144, (s.regs 4).toNat + 24)])
      | .panicked v s' => ∃ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e ∧
        v = ⟨s.mem.readLE (s.mem.readLE (errAddrOf e) 8 + 8) 8, s.mem.readLE (errAddrOf e + 8) 8⟩
      | .goexited _ => False := by
  refine ⟨impl, rt, H, hpp, 4, (Janus.Contracts.PanicModel.P0 [] 0), ret, s0, hnew, hret, setup, ?w3,
    correctness (Janus.Contracts.PanicModel.P0 [] 0) impl rt H hpp 4 hnew ret hret s0 setup ?w3⟩
  case w3 => exact ⟨trivial, pre⟩

end Witness

end Fv256.Amd64.MustFromHex
