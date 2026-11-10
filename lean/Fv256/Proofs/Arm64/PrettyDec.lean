import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.UtilE64
import Fv256.Proofs.Common.StrE
import Fv256.Proofs.Common.PdCells
import Fv256.Proofs.Arm64.Pd.Lift
import Fv256.Spec.Arm64.PrettyDec

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.PrettyDec

set_option maxRecDepth 100000 in
theorem hLib : Fv256.Arm64.LinkEq.LibIn Fv256.Arm64.PrettyProg.program Extracted.program :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option maxRecDepth 100000 in
theorem pdE_entry : Fv256.Arm64.Pd.pdE = Extracted.entry := by unfold Fv256.Arm64.Pd.pdE; decide

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
/-- `PrettyDec(separator)` returns the decimal digits of `*z` with `separator` between every three digits counted from
the right (`1234567` becomes `1,234,567` for `','`), and `"0"` for zero.  The result is the string at `(X0, X1)`. -/
theorem correctness_proof (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z sep : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, sep]
      (fun s => GuardOK s 704 ∧ StackOK s 4608 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4608) (4608 + 24) rt ∧ Ptr32 s.mem z false ∧
        (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
        (val256 s.mem z.toNat ≠ 0 →
          H [0, s.sp.toNat - 168 - plen (val256 s.mem z.toNat), plen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt s.mem)))
      (fun s s' => StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (prettyBytes (sep.toNat % 256) (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)])) := by
  rw [← pdE_entry]
  refine Fv256.Arm64.Pd.ensures_of_summary' (Fv256.Arm64.Pd.pd_summary_E _ hLib rfl impl rt H z sep hc) ?_ ?_
  · intro ret s hret hs ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hl : s.regs 30 = BitVec.ofNat 64 ret := hs.lr
    have hrl : (s.regs 30).toNat = ret := by
      rw [hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hret.user; omega)]
    exact ⟨hs.args 0 (by simp), hs.args 1 (by simp), h1, h2, h3, h4, h5, h6, h7, h8, by rw [hrl]; exact hret.user,
      by rw [hrl]; exact hret.aligned⟩
  · intro ret s s' hret hs hp hq
    exact ⟨⟨hq.2.1, hq.2.2.2.1, hq.2.2.1, hq.2.2.2.2.1⟩, hq.1, hq.2.2.2.2.2⟩

namespace Wit

open Janus.Contracts.Sat

/-- The readiness of the witness: the call is `slicebytetostring(nil, p, 5)` and the heap block is writable and
disjoint from the callee's stack window. -/
def H1 : RtReady := fun a _ sp v => arg a 0 = 0 ∧ arg a 2 = 5 ∧ v.accessible HEAP 5 true = true ∧ (HEAP + 5 ≤ sp - 4096 ∨ sp + 32 ≤ HEAP)

/-- `slicebytetostring(nil, p, 5)`: read the five bytes, copy them to the heap block, return `(HEAP, 5)`. -/
def copyCode : List Nat :=
  [0x39400023, 0x39400424, 0x39400825, 0x39400c26, 0x39401027, 0xd2a00088, 0x39000103, 0x39000504, 0x39000905,
    0x39000d06, 0x39001107, 0xaa0803e0, 0xd28000a1, 0xd65f03c0]

def implAt : List Segment := [{ name := "model", base := ssAddr, words := copyCode }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract (Extracted.program.link implAt) ssAddr rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, hsb⟩, hpre, -, -, hH⟩
  have ha := ready_of rfl hH
  simp [Ready, H1, arg, slicebytetostringSpec, argWords, wordsFrom] at hpre ha
  obtain ⟨ha0, ha2, hHeap, hHdis⟩ := ha
  obtain ⟨-, ⟨hsn, hsacc⟩, -⟩ := hpre
  rw [ha2] at hsn hsacc
  have hsacc' := hsacc (by omega)
  janus_run
  have hargs : argWords s 3 = [(s.regs 0).toNat, (s.regs 1).toNat, (s.regs 2).toNat] := by
    simp [argWords, wordsFrom]
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg_apply])
  · repeat' first
      | exact MemFrame.refl _ _
      | refine MemFrame.writeLE ?_ _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP, rtIf]) (by simp [HEAP]) (by simp [HEAP])
  · simp only [hargs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    refine ⟨⟨ha2.symm, ?_, ?_⟩, ?_⟩
    · exact Janus.Arm64.Memory.accessible_sub s.mem h_num0 (Or.inl rfl) (by omega) (by omega)
    · rw [ha2]
      simp [strBytes, List.range_succ, Janus.Arm64.Memory.bytes_writeLE, HEAP]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact BitVec.isLt _
    · simp [StrAt, ha0, ha2, InRanges, rtW, HEAP]

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

/-- the receiver holds `1000` (so `PrettyDec(',')` is `"1,000"`) -/
def bytes (a : Nat) : Byte :=
  if a = zp then 0xe8 else if a = zp + 1 then 0x03 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def argz : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then argz else if i = 1 then 44 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4608, 4608 + 24, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨HEAP, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [argz, 44] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide +kernel

theorem dl1000 : decLen 1000 = 4 := decLen_of 1000 4 (by omega) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 704 ∧ StackOK s0 4608 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4608) (4608 + 24) rtW ∧ Ptr32 s0.mem argz false ∧
    (argz.toNat + 32 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 24 ≤ argz.toNat) ∧
    ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4608 ∨ s0.sp.toNat + 24 ≤ (s0.regs 28).toNat + 16) ∧
    (val256 s0.mem argz.toNat ≠ 0 →
      H1 [0, s0.sp.toNat - 168 - plen (val256 s0.mem argz.toNat), plen (val256 s0.mem argz.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 400) (rtView rtW s0.mem)) := by
  have hz : val256 s0.mem argz.toNat = 1000 := by
    unfold val256 s0 argz zp
    decide
  have hp : plen (val256 s0.mem argz.toNat) = 5 := by
    simp only [hz, plen, dl1000]
  refine ⟨by unfold GuardOK; decide, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · rw [hp]
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/PrettyDec.lean
def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 HEAP else if i = 2 then BitVec.ofNat 64 5 else s0.regs i }
/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `slicebytetostring(nil, HEAP, 5)` at its entry, in the caller's frame (`SP = sp0 - 400`). -/
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 400), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show H1 (argWords csSb 3) (csSb.regs 28).toNat csSb.sp.toNat (rtView rtW csSb.mem)
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address, copying the five bytes of `"1,000"`) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z sep : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, sep] s ∧
    (GuardOK s 704 ∧ StackOK s 4608 24 ∧ Extracted.program.DataLoaded s.mem ∧
      Outside (s.sp.toNat - 4608) (4608 + 24) rt ∧ Ptr32 s.mem z false ∧
      (z.toNat + 32 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ z.toNat) ∧
      ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4608 ∨ s.sp.toNat + 24 ≤ (s.regs 28).toNat + 16) ∧
      (val256 s.mem z.toNat ≠ 0 →
        H [0, s.sp.toNat - 168 - plen (val256 s.mem z.toNat), plen (val256 s.mem z.toNat)]
          (s.regs 28).toNat (s.sp.toNat - 400) (rtView rt s.mem))) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (prettyBytes (sep.toNat % 256) (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4608, s.sp.toNat - 8), (s.sp.toNat + 16, s.sp.toNat + 17)]) := by
  refine ⟨implAt, rtW, H1, ret, s0, argz, 44, model, ?w1, ?w2, pre,
    ⟨csSb, rfl, csSb_pre⟩,
    correctness_proof implAt rtW H1 argz 44 model ret ?w1 s0 ?w2 pre⟩
  case w1 => exact by rw [linked_eq]; exact hret
  case w2 => exact by rw [linked_eq]; exact setup
end Wit

end Fv256.Arm64.PrettyDec
