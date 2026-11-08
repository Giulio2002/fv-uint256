import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.GrabTac
import Fv256.Amd64.DecExt

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec

namespace Fv256.Amd64.String

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s (0x378 + 24) ∧ StackWritable s 4592 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4592) (4592 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 24 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 24 - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 24 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 24 - 384 - 0x58) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hout, hrt1, hrt2, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1⟩
  janus64_intro hs
  have hdE : decE = 4931168 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run [hdE] calls [dec_summary_ext impl rt H z hc]
  grab_const Fv256.E.decBytes as hstr
  grab_const Janus.MemFrame as hfrm
  simp (disch := omega) only [valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hstr
  refine ⟨by simpa [valueAt] using hstr, ?_⟩
  have h1 : MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 24) 8 4928979)
      (rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)]) := by
    refine MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)])
      (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
      (MemFrame.of_writeLE _ _ (rs := rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
    intro a n h; exact ⟨h, h⟩
  have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)]) hfrm (fun a n h => by
    simp only [outside_append, outside_cons] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, by omega, trivial⟩)
  exact h1.trans h2 fun a n h => ⟨h, h⟩

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (rtW H0)

def implAt : List Amd64.Segment := [{ name := "model", base := ssAddr, bytes := constCode64 0 0 0 }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) ssAddr rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, -, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, H0, arg, List.getD_eq_getElem?_getD] at ha
  janus64_run
  apply rtPost_const <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  simp only [slicebytetostringSpec] at ha ⊢
  simp [ha, Spec.strBytes, StrAt]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4592, 4592 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 (0x378 + 24) ∧ StackWritable s0 4592 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4592) (4592 + 8) rtW ∧ Outside 5163273 256 rtW ∧ Outside 5176582 256 rtW ∧
    (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4592 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4592 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s0.mem.readLE arg.toNat 32 →
      H0 [0, (s0.regs 4).toNat - 24 - 0x178 + 86 + (98 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 24 - 0x178 - 8) (rtView rtW s0.mem)) ∧
    (100 ≤ s0.mem.readLE arg.toNat 32 → s0.mem.readLE arg.toNat 32 < 2 ^ 64 →
      H0 [0, (s0.regs 4).toNat - 24 - 384 - 0x20 + (24 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 24 - 384 - 0x58) (rtView rtW s0.mem)) := by
  have hz : s0.mem.readLE arg.toNat 32 = 0 := by
    unfold s0 arg zp
    decide
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => ?_, fun h _ => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hz] at h; exact absurd h (by decide)
  · rw [hz] at h; exact absurd h (by decide)

/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `s0`'s memory at the stub's entry, `RSP` 64 below
`s0`'s (inside the stack window), all argument words zero (`H0`). -/
def csSs : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 4 then s0.regs 4 - 64#64 else s0.regs i }

theorem csSs_rip : csSs.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSs_pre : RtPre64 rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSs := by
  have hargs : argWords64 csSs 3 = [0, 0, 0] := by
    unfold argWords64 csSs; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    simp
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    exact ⟨Or.inl (by simp), Or.inl (by simp), trivial⟩
  · split
    · show ∀ j, Contracts.arg (argWords64 csSs 3) j = 0
      intro j; rw [hargs]; simp only [Contracts.arg]
      rcases j with _ | _ | _ | j <;> simp
    · trivial

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧
      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 24) ∧ StackWritable s 4592 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4592) (4592 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4592 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      H [0, (s.regs 4).toNat - 24 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 24 - 0x178 - 8) (rtView rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (s.regs 4).toNat - 24 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 24 - 384 - 0x58) (rtView rt s.mem))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4592, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt, rtW, H0, ret, s0, arg, model, ⟨csSs, csSs_rip, csSs_pre⟩, ?w1, ?w2, pre,
    correctness implAt rtW H0 arg model ret ?w1 s0 ?w2 pre⟩
  case w1 => exact by rw [linked_eq]; exact hret
  case w2 => exact by rw [linked_eq]; exact setup

end Witness

end Fv256.Amd64.String
