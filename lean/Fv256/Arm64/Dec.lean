import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.Arm64.DecExt

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Dec

set_option maxRecDepth 100000 in

theorem decE_entry : decE = Extracted.entry := by unfold decE; decide
set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)])) := by
    rw [← decE_entry]
    refine ensures_of_summary (dec_summary_ext impl rt H z hc) ?_ ?_
    · intro ret s hret hs ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
      have hl : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
      have hrl : (s.regs 30).toNat = ret := by
        rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
      exact ⟨hs.args 0 (by simp), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by rw [hrl]; exact hret.user,
        by rw [hrl]; exact hret.aligned⟩
    · intro ret s s' hret hs hp hq
      exact ⟨⟨hq.2.1, hq.2.2.2.1, hq.2.2.1, hq.2.2.2.2.1⟩, hq.1, hq.2.2.2.2.2.1.mono (fun a n h => by
        simp only [outside_append, outside_cons] at h ⊢
        exact ⟨h.1, by omega, trivial⟩)⟩

namespace Witness

open Janus.Contracts.Sat

def implAt : List Segment := [{ name := "model", base := ssAddr, words := constCode 0 0 0 }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) ssAddr rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, H0, arg, List.getD_eq_getElem?_getD, slicebytetostringSpec] at ha
  janus_run
  apply rtPost_const <;> (try rfl) <;> (try simp [setReg])
  simp [ha, strBytes, StrAt]

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4608, 4608 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide +kernel

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 688 ∧ StackOK s0 4608 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4608) (4608 + 8) rtW ∧ Outside 989280 256 rtW ∧ Outside 1002589 256 rtW ∧
    Ptr32 s0.mem arg false ∧ (arg.toNat + 32 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 8 ≤ (s0.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s0.mem arg.toNat →
      H0 [0, s0.sp.toNat - 384 + 94 + (98 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 384) (rtView rtW s0.mem)) ∧
    (100 ≤ val256 s0.mem arg.toNat → val256 s0.mem arg.toNat < 2 ^ 64 →
      H0 [0, s0.sp.toNat - 384 - 32 + (24 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 384 - 96) (rtView rtW s0.mem)) := by
  have hz : val256 s0.mem arg.toNat = 0 := by
    unfold val256 s0 arg zp
    decide
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => ?_, fun h _ => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hz] at h; exact absurd h (by decide)
  · rw [hz] at h; exact absurd h (by decide)

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/Dec.lean
def csSb0 : State := {{ s0 with regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0 }}
/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): at its entry, the empty string (`buf = nil, ptr = 0, n = 0`: every argument word is `0`, as `H0` asks). -/
def csSb : State := {{ csSb0 with sp := BitVec.ofNat 64 (sp0 - 32), pc := BitVec.ofNat 64 ssAddr }}

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), by decide, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Ready H0 rtW (argWords csSb 3) csSb
    intro j
    simp [argWords, wordsFrom, arg, csSb, csSb0]

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 688 ∧ StackOK s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4608) (4608 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 384 - 96) (rtView rt s.mem))) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat + 8)]) := by
  refine ⟨implAt, rtW, H0, ret, s0, arg, model, ?w1, ?w2, pre,
    ⟨csSb, rfl, csSb_pre⟩,
    correctness implAt rtW H0 arg model ret ?w1 s0 ?w2 pre⟩
  case w1 => exact by rw [linked_eq]; exact hret
  case w2 => exact by rw [linked_eq]; exact setup
end Witness

end Fv256.Arm64.Dec
