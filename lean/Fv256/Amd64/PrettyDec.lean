import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.PdCells
import Fv256.Amd64.Pd.Lift

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E

namespace Fv256.Amd64.PrettyDec

/-- the address of `runtime.slicebytetostring` in the extracted program -/
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem hLib : Fv256.LinkEq.LibIn Fv256.PrettyProg.program Extracted.program :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem pdE_entry : Fv256.Amd64.Pd.pdE = Extracted.entry := by unfold Fv256.Amd64.Pd.pdE; decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- `PrettyDec(separator)` returns the decimal digits of `*z` with `separator` between every three digits counted from
the right (`1234567` becomes `1,234,567` for `','`), and `"0"` for zero.  The result is the string at `(RAX, RBX)`. -/
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, sep]
      (fun s => StackGuardOK s 0x378 ∧ StackWritable s 4576 0x18 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4576) (4576 + 0x18) rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16) ∧
        (valueAt s z 32 ≠ 0 →
          H [0, (s.regs 4).toNat - 0xa8 - plen (valueAt s z 32), plen (valueAt s z 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x188) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (prettyBytes (sep.toNat % 256) (valueAt s z 32)) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4576, (s.regs 4).toNat + 0x18)])) := by
  rw [← pdE_entry]
  exact ensures_of_summary64 (Fv256.Amd64.Pd.pd_summary_E _ hLib rfl impl rt H z sep hc)
    (fun ret s hret hs ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ =>
      ⟨hs.args 0 (by simp), hs.args 1 (by simp), h1, h2, h3, h4, h5, h6, h7, h8, h9, hs.zero, hs.df, by
        have := hs.ret
        rw [this]
        exact Nat.lt_of_lt_of_le hret.user (by decide)⟩)
    (fun ret s s' hret hs hp hq => ⟨⟨hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1⟩, hq.1, hq.2.2.2.2.2⟩)


namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (rtW HEAP)

/-- The readiness of the witness: the call is `slicebytetostring(nil, p, 5)` and the heap block is writable. -/
def H1 : RtReady := fun a _ sp v => arg a 0 = 0 ∧ arg a 2 = 5 ∧ v.accessible HEAP 5 true = true ∧ (HEAP + 5 ≤ sp - 4096 ∨ sp + 32 ≤ HEAP)

/-- `slicebytetostring(nil, p, 5)`: read the five bytes, copy them to the heap block, return `(HEAP, 5)`. -/
def copyCode : List Nat :=
  [0x44, 0x0F, 0xB6, 0x03, 0x44, 0x0F, 0xB6, 0x4B, 0x01, 0x44, 0x0F, 0xB6, 0x53, 0x02, 0x44, 0x0F, 0xB6, 0x5B, 0x03,
    0x44, 0x0F, 0xB6, 0x63, 0x04] ++ [0xBF] ++ le32 HEAP ++
  [0x44, 0x88, 0x07, 0x44, 0x88, 0x4F, 0x01, 0x44, 0x88, 0x57, 0x02, 0x44, 0x88, 0x5F, 0x03, 0x44, 0x88, 0x67, 0x04] ++
  [0xB8] ++ le32 HEAP ++ [0xBB, 5, 0, 0, 0, 0xC3]

def implAt : List Amd64.Segment := [{ name := "model", base := ssAddr, bytes := copyCode }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) ssAddr rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, hpre, -, -, hH⟩
  have ha := ready_of rfl hH
  simp [Ready64, H1, arg, slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hpre ha
  obtain ⟨ha0, ha2, hHeap, hHdis⟩ := ha
  obtain ⟨-, ⟨hsn, hsacc⟩, -⟩ := hpre
  rw [ha2] at hsn hsacc
  have hsacc' := hsacc (by omega)
  janus64_run
  have hargs : argWords64 s 3 = [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] := by
    simp [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs]
  have hrt : ((HEAP, HEAP + 0x10000)) ∈ rtW := by simp [rtW, HEAP]
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf, setRegF_apply])
  · simp only [hargs]
    simp [ha0, rtIf]
    refine ((MemFrame.refl _ _).writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP])).writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP]) |>.writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP]) |>.writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP]) |>.writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP])
  · simp only [hargs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    refine ⟨⟨ha2.symm, ?_, ?_⟩, ?_⟩
    · exact Janus.Arm64.Memory.accessible_sub s.mem h_num1 (Or.inl rfl) (by omega) (by omega)
    · rw [ha2]
      simp [Spec.strBytes, List.range_succ, Janus.Arm64.Memory.bytes_writeLE, HEAP]
    · simp [StrAt, ha0, ha2, InRanges, rtW, HEAP]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

/-- the receiver holds `1000` (so `PrettyDec(',')` is `"1,000"`) and the return address is `0x200000` -/
def bytes (a : Nat) : Byte :=
  if a = zp then 0xe8 else if a = zp + 1 then 0x03 else if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 3 then 44 else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4576, 4576 + 0x18, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨HEAP, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg, 44] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_, rfl⟩
  intro i h
  have h2 : i < 2 := by simpa using h
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem dl1000 : decLen 1000 = 4 := decLen_of 1000 4 (by omega) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0x378 ∧ StackWritable s0 4576 0x18 ∧ Extracted.program.DataLoaded s0.mem ∧
        Outside ((s0.regs 4).toNat - 4576) (4576 + 0x18) rtW ∧
        (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
        (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4576 ∨ (s0.regs 4).toNat + 0x18 ≤ arg.toNat) ∧
        ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4576 ∨ (s0.regs 4).toNat + 0x18 ≤ (s0.regs 14).toNat + 16) ∧
        (valueAt s0 arg 32 ≠ 0 →
          H1 [0, (s0.regs 4).toNat - 0xa8 - plen (valueAt s0 arg 32), plen (valueAt s0 arg 32)]
            (s0.regs 14).toNat ((s0.regs 4).toNat - 0x188) (rtView rtW s0.mem)) := by
  have hz : s0.mem.readLE arg.toNat 32 = 1000 := by
    unfold s0 arg zp
    decide
  have hp : plen (valueAt s0 arg 32) = 5 := by
    simp only [valueAt, hz, plen, dl1000]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun hn => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hp]
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address, copying the five bytes of `"1,000"`) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z sep : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, sep] s ∧
    (StackGuardOK s 0x378 ∧ StackWritable s 4576 0x18 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4576) (4576 + 0x18) rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4576 ∨ (s.regs 4).toNat + 0x18 ≤ (s.regs 14).toNat + 16) ∧
        (valueAt s z 32 ≠ 0 →
          H [0, (s.regs 4).toNat - 0xa8 - plen (valueAt s z 32), plen (valueAt s z 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 0x188) (rtView rt s.mem))) :=
  ⟨implAt, rtW, H1, ret, s0, arg, 44, model, by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setup, pre⟩

end Witness

end Fv256.Amd64.PrettyDec
