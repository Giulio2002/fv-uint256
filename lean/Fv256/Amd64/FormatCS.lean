import Extracted
import Fv256.Amd64.FormatWitA
import Fv256.Amd64.FormatNil
import Fv256.Amd64.FormatInhabit
import Fv256.Amd64.CallSites.Base
import Fv256.Amd64.CallSites.Live

/-!
# `Format` (amd64): the call-site states of the twelve contract hypotheses (U-WITNESS-CALLSITE)

One universal environment `memU` / `sU` (the `IfaceModel.R0` metadata, the toy allocator's heap and bump word, the two string-runtime blocks, the
extracted data, a stack at `[0x40000, 0x50000)`, the goroutine at `0x50000`) serves the runtime stubs (`runtime.typeAssert`, `newobject`,
`gcWriteBarrier1/2`, `slicebytetostring`, `stringtoslicebyte`); the indirect calls (`ICallPre64`) use the flat memory of `Fv256.Inhab`.
Each lemma is the conjunct `∃ s_c, s_c.rip = entry ∧ pre s_c` of the three witnesses (`FormatWitB`, `FormatWitBig`, `FormatWitN`), at `z = 16` (fast and big paths) or `z = 0` (nil).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Toy
open Janus.Contracts.IfaceModel Janus.Spec.Type
open Fv256.Amd64.FormatWitA Fv256.CallSites Fv256.Inhab

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Amd64.FormatCS

/-- the precondition of `runtime.typeAssert` as one conjunct (the contract's own `pre`) -/
@[reducible] def TypeAssertSite (R : IfaceModel) (H : RtReady) (s : State) : Prop :=
  Janus.Contracts.IfaceAmd64.RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      (s.regs 3).toNat ≠ 0 ∧
      ((s.regs 3).toNat ≠ 0 → R.IsType (s.regs 3).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 3).toNat).isSome)) ∧
      Ready64 H R.priv [(s.regs 0).toNat, (s.regs 3).toNat] s

/-! ### the universal environment -/

def dsegsU : List DataSegment := Extracted.data
def dregsU : List Region := dsegsU.map (fun d => ⟨d.base, d.bytes.length, false⟩)
def tblU : List (Nat × Nat) := (BUMP + 3, 0x10) :: wtable

def bytesU (a : Nat) : Byte :=
  match dsegsU.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((tblU.lookup a).getD 0)

def memU : Memory :=
  ⟨bytesU, wmem.regions ++ [⟨hA, 8, true⟩, ⟨hB, 8, true⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩] ++ dregsU⟩

def sU : State :=
  { regs := fun i => if i = 14 then BitVec.ofNat 64 wg else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := 0, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := memU }

theorem envU (g : W64) : Env0 memU g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem descU : TADescOK R0 memU DTA := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by simp only [R0_isInter, taInter]; decide +kernel, ?_⟩
  show TACacheOK R0 memU (memU.readLE DTA 8) (taInter memU DTA)
  rw [show memU.readLE DTA 8 = TAC by decide +kernel]
  exact TACacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem rtpreU (s : State) (hm : s.mem = memU) (h14 : s.regs 14 = BitVec.ofNat 64 wg) (h4 : s.regs 4 = BitVec.ofNat 64 wsp)
    (hx : s.xmm 15 = 0) (hdf : s.df = false) (n : Nat) (hn : n ≤ 3) : Janus.Contracts.IfaceAmd64.RTPre R0 n s := by
  have hw : memU.accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide +kernel
  refine ⟨hm ▸ envU (s.regs 14), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, hx, hdf, ?_, ?_⟩
  · simp only [regG, stackguard0Offset, h14]; decide
  · simp only [regG, stackguard0Offset, h14, hm]; decide +kernel
  · simp only [stackguard0, regG, regSP, stackguard0Offset, h14, h4, hm, R0_depth]; decide +kernel
  · simp only [h4]; decide
  · simp only [h4, R0_depth]; decide
  · simp only [h4]; simp [wsp]; omega
  · simp only [h4, hm, R0_depth, BitVec.toNat_ofNat]
    exact Janus.Arm64.Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [h4, hm]; decide +kernel
  · simp only [h4, R0_depth, R0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

theorem rt_eq : R2.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem lookup_none {l : List (Nat × Nat)} {i : Nat} (h : ∀ p ∈ l, p.1 ≠ i) : l.lookup i = none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨k, v⟩ := a
    have hk : k ≠ i := h (k, v) (by simp)
    have hb : (i == k) = false := by simpa [beq_iff_eq] using Ne.symm hk
    simp only [List.lookup, hb]
    exact ih (fun p hp => h p (by simp [hp]))

theorem inv0U : R2.inv 0x400 [] (sU.regs 14).toNat (view R2.rt [] sU.mem) := by
  have hbump : memU.readLE BUMP 8 = HEAP := by decide +kernel
  refine toyInv_init (m := memU) (g := (sU.regs 14).toNat) (by decide) hbump (fun i hi hi' => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  show bytesU i = 0
  have h1 : 0x10000000 ≤ i := by simp only [HEAP] at hi; omega
  unfold bytesU
  have hn : dsegsU.find? (fun d => decide (d.base ≤ i ∧ i < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
    have := h2 d hd
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    omega
  rw [hn]
  have hl : tblU.lookup i = none := lookup_none (fun p hp => by
    have : ∀ q ∈ tblU, q.1 < 0x500000 := by decide
    have := this p hp; omega)
  rw [hl]; rfl

/-! ### the runtime stubs -/

def csTA0 : State := { sU with regs := fun i => if i = 0 then BitVec.ofNat 64 DTA else if i = 3 then BitVec.ofNat 64 TD else sU.regs i }
def csTA : State := { csTA0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") }

set_option maxRecDepth 100000 in
theorem csTA_pre : TypeAssertSite R0 Hw csTA := by
  refine ⟨rtpreU csTA rfl rfl rfl rfl rfl 2 (by decide), ?_, by decide, fun _ => ⟨Or.inl rfl, Or.inl (by decide +kernel)⟩, ?_⟩
  · exact descU
  · show Hw [csTA.regs 0 |>.toNat, csTA.regs 3 |>.toNat] _ _ (rtView R0.priv csTA.mem)
    simp only [Hw]
    refine ⟨Or.inr ⟨_, _, rfl⟩, ?_, ?_, Or.inl (by decide +kernel), Or.inl (by decide +kernel)⟩ <;>
      rw [Janus.Arm64.Memory.accessible_congr rfl] <;> decide +kernel

def csNew0 : State := { sU with regs := fun i => if i = 0 then BitVec.ofNat 64 Fv256.Amd64.IntoBig.bigType else sU.regs i }
def csNew : State := { csNew0 with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csW1 : State := { sU with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { sU with rip := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, ⟨by decide +kernel, ?_⟩, ?_, inv0U, by decide +kernel, liveSep_nil _, ?_⟩
  · simp only [calleeStack64, outside_cons, outside_nil]; decide +kernel
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · rw [rt_eq]; intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide +kernel)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 :=
  ⟨by decide +kernel, by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0U, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide +kernel)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 :=
  ⟨by decide +kernel, by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0U, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide +kernel)⟩

/-! ### the string runtime: `slicebytetostring(nil, VAL, 2)` and `stringtoslicebyte(nil, VAL, 2)` -/

def csStr0 : State := { sU with regs := fun i => if i = 3 then BitVec.ofNat 64 VAL else if i = 1 then 2 else sU.regs i }
def csSs : State := { csStr0 with rip := BitVec.ofNat 64 ssAddr }
def csSt : State := { csStr0 with rip := BitVec.ofNat 64 stAddr }

theorem csStr_ready (s : State) (hargs : argWords64 s 3 = [0, VAL, 2]) (hsp : s.regs 4 = BitVec.ofNat 64 wsp) (hm : s.mem = memU) :
    Ready64 Hw rtT (argWords64 s 3) s := by
  show Hw (argWords64 s 3) _ _ (rtView rtT s.mem)
  rw [hargs]
  simp only [Hw]
  refine ⟨Or.inl (Or.inl ⟨_, rfl⟩), ?_, ?_, Or.inl ?_, Or.inl ?_⟩
  · rw [rtView_acc, hm]; decide +kernel
  · rw [rtView_acc, hm]; decide +kernel
  · rw [hsp]; decide +kernel
  · rw [hsp]; decide +kernel

set_option maxRecDepth 100000 in
theorem csSs_pre : RtPre64 rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSs := by
  have hargs : argWords64 csSs 3 = [0, VAL, 2] := by
    unfold argWords64 csSs csStr0 sU; decide +kernel
  refine ⟨by decide +kernel, ?_, ?_, trivial, ready_intro rfl (csStr_ready csSs hargs rfl rfl)⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide +kernel), by decide +kernel, fun h => absurd (by decide +kernel) h⟩
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; decide +kernel

set_option maxRecDepth 100000 in
theorem csSt_pre : RtPre64 rtT 4096 Hw stringtoslicebyteSpec csSt := by
  have hargs : argWords64 csSt 3 = [0, VAL, 2] := by
    unfold argWords64 csSt csStr0 sU; decide +kernel
  refine ⟨by decide +kernel, ?_, ?_, trivial, ready_intro rfl (csStr_ready csSt hargs rfl rfl)⟩
  · simp only [stringtoslicebyteSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide +kernel), by decide +kernel, fun h => absurd (by decide +kernel) h⟩
  · simp only [stringtoslicebyteSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; decide +kernel

/-! ### the indirect calls (flat memory) -/

theorem outside_far (above : Nat) (h : above ≤ 200) : Outside (2 ^ 40) above rtT := by
  simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]
  omega

theorem ic_true (pc nargs : Nat) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ 80) :
    ICallPre64 nargs 4608 80 rtT (fun _ => True) (callSt64At (BitVec.ofNat 64 pc) 0 0 0 0 0 flatMem) :=
  callSt64At_pre (m := flatMem) rfl (by simp [readLE_flatMem]) (by omega) hn hab (outside_far 80 (by omega)) trivial

/-- the `Write` call: the slice holds `bs` -/
theorem wr_pre (pc : Nat) (data : BitVec 64) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (hl : bs.length ≤ 2 ^ 20) :
    ICallPre64 4 4608 80 rtT (Fv256.FormatFast.FastWP data bs)
      (callSt64At (BitVec.ofNat 64 pc) data (BitVec.ofNat 64 bs.length) 0x2000 0 (BitVec.ofNat 64 bs.length) (strMem bs 0x2000)) := by
  have hm : (strMem bs 0x2000).regions = [⟨0, 2 ^ 48, true⟩] := rfl
  have hlen : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hret : (strMem bs 0x2000).readLE (2 ^ 40) 8 < 2 ^ 47 := by
    rw [readLE_strMem_far _ _ _ _ (by omega)]; omega
  refine callSt64At_pre hm hret (by omega) (by omega) (by omega) (outside_far 80 (by omega)) ?_
  refine ⟨rfl, ?_, ?_⟩
  · simp only [callSt64At_r1, callSt64At_r3, callSt64At_mem, hlen]
    have := strOut_strMem bs hb 0x2000 (by omega)
    simpa using this
  · simp only [callSt64At_r1, callSt64At_r7, hlen]; exact Nat.le_refl _

theorem fb16 (ch : BitVec 64) (hch : ch.toNat % 2 ^ 32 ≠ 120) : Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32) = [49, 54] := by
  have h1 : Fv256.E.decBytes 16 = [49, 54] := by
    rw [Fv256.E.decBytes_ge 16 (by omega)]
    simp [Fv256.E.decBytes_lt 1 (by omega), Fv256.E.decBytes_lt 6 (by omega)]
  simp [Fv256.FormatSpec.fastBytes, h1, hch]

theorem fb0 (ch : BitVec 64) (hch : ch.toNat % 2 ^ 32 ≠ 120) : Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32) = [48] := by
  simp [Fv256.FormatSpec.fastBytes, Fv256.E.decBytes, hch]

open Fv256.Amd64.FormatNil in
/-- the flat memory of the `Fprint` call: the string literal, its header and descriptor word as `FpArg` asks -/
def m_fp : Memory := ((((strMem Fv256.FormatSpec.nilText litA).writeLE (2 ^ 40 + 56) 8 strTyA).writeLE (2 ^ 40 + 64) 8 hdrA).writeLE
    hdrA 8 litA).writeLE (hdrA + 8) 8 5

open Fv256.Amd64.FormatNil in
/-- `fmt.Fprint(w, "<nil>")`: the property `FpArg data` over the extraction's addresses -/
theorem fp_pre (pc : Nat) (data : BitVec 64) :
    ICallPre64 5 4608 80 rtT (FpArg data)
      (callSt64At (BitVec.ofNat 64 pc) 0 (BitVec.ofNat 64 (2 ^ 40 + 56)) data 1 1 m_fp) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40 + 56)).toNat = 2 ^ 40 + 56 := by simp
  have hsp' : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  have h1 : strTyA < 2 ^ 64 := by decide
  have h2 : hdrA < 2 ^ 64 := by decide
  have h3 : litA < 2 ^ 64 := by decide
  have hd1 : litA + 5 ≤ 2 ^ 40 := by decide
  have hd2 : hdrA + 16 ≤ 2 ^ 40 := by decide
  have hd3 : litA + 5 ≤ hdrA ∨ hdrA + 16 ≤ litA := by decide
  have hm : m_fp.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_fp, strMem]
  have hret : m_fp.readLE (2 ^ 40) 8 < 2 ^ 47 := by
    simp (disch := omega) only [m_fp, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [readLE_strMem_far _ _ _ _ (by simp [Fv256.FormatSpec.nilText]; omega)]; omega
  refine callSt64At_pre hm hret (by omega) (by omega) (by omega) (outside_far 80 (by omega)) ?_
  simp only [FpArg, callSt64At_r1, callSt64At_r3, callSt64At_r4, callSt64At_r6, callSt64At_r7, callSt64At_mem, hsp, hsp']
  refine ⟨trivial, rfl, rfl, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [m_fp, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h1)
  · simp (disch := omega) only [m_fp, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h2)
  · simp (disch := omega) only [m_fp, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h3)
  · simp (disch := omega) only [m_fp, Janus.Arm64.Memory.readLE_writeLE_self]
  · have := strOut_strMem Fv256.FormatSpec.nilText (by simp [Fv256.FormatSpec.nilText]) litA (by simp [Fv256.FormatSpec.nilText]; omega)
    simp only [m_fp]
    refine strOut_writeLE (strOut_writeLE (strOut_writeLE (strOut_writeLE this _ _ _ ?_) _ _ _ ?_) _ _ _ ?_) _ _ _ ?_ <;>
      simp [Fv256.FormatSpec.nilText] <;> omega

/-- the receiver `P = 0x2000` of `(*big.Int).Format` holds `zv`: `len = 0` (`zv = 0`) or one limb (`zv = 16`) -/
def m_bf0 : Memory := flatMem.writeLE (0x2000 + 24) 8 4
def m_bf16 : Memory := (((flatMem.writeLE (0x2000 + 24) 8 4).writeLE (0x2000 + 16) 8 1).writeLE (0x2000 + 8) 8 0x3000).writeLE 0x3000 8 16

theorem bf_pre0 (pc : Nat) (tab data ch : BitVec 64) :
    ICallPre64 4 4608 80 rtT (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat 0 ∧ sc.regs 3 = tab ∧
      sc.regs 1 = data ∧ (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32)
      (callSt64At (BitVec.ofNat 64 pc) 0x2000 data tab 0 ch m_bf0) := by
  have hm : m_bf0.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_bf0, flatMem]
  have hret : m_bf0.readLE (2 ^ 40) 8 < 2 ^ 47 := by
    simp (disch := omega) only [m_bf0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]; omega
  refine callSt64At_pre hm hret (by omega) (by omega) (by omega) (outside_far 80 (by omega)) ?_
  refine ⟨0x2000, by simp, ?_, by simp, by simp, by simp⟩
  simp only [callSt64At_mem]
  have h2k : (0x2000 : BitVec 64).toNat = 0x2000 := by decide
  rw [h2k]
  refine ⟨0, 0, 4, ?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, by omega, by omega, Or.inl rfl, rfl⟩
  · simp [m_bf0]; exact accessible_flat flatMem rfl _ _ _ (by omega)
  · simp (disch := omega) only [m_bf0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Janus.Arm64.Memory.readLE_writeLE_self]
  · simp [m_bf0]; exact accessible_flat flatMem rfl _ _ _ (by omega)

theorem bf_pre16 (pc : Nat) (tab data ch : BitVec 64) :
    ICallPre64 4 4608 80 rtT (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat 16 ∧ sc.regs 3 = tab ∧
      sc.regs 1 = data ∧ (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32)
      (callSt64At (BitVec.ofNat 64 pc) 0x2000 data tab 0 ch m_bf16) := by
  have hm : m_bf16.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_bf16, flatMem]
  have hret : m_bf16.readLE (2 ^ 40) 8 < 2 ^ 47 := by
    simp (disch := omega) only [m_bf16, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]; omega
  refine callSt64At_pre hm hret (by omega) (by omega) (by omega) (outside_far 80 (by omega)) ?_
  refine ⟨0x2000, by simp, ?_, by simp, by simp, by simp⟩
  simp only [callSt64At_mem]
  have h2k : (0x2000 : BitVec 64).toNat = 0x2000 := by decide
  rw [h2k]
  refine ⟨0x3000, 1, 4, ?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, by omega, by omega, Or.inr ?_, ?_⟩
  all_goals first
    | (simp (disch := omega) only [Fv256.C.bigAbs, m_bf16, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, readLE_flatMem] <;> decide)
    | (simp [m_bf16]; exact accessible_flat flatMem rfl _ _ _ (by omega))

-- AGGREGATE-BEGIN (scripts/cs_format_amd64.py)

theorem csAll16 (tab data ch : BitVec 64) (hch : ch.toNat % 2 ^ 32 ≠ 120) :
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Amd64.FormatCS.TypeAssertSite R0 Hw s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre64 rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre64 rtT 4096 Hw stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 1 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 1 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 2 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 4 4608 80 rtT (Fv256.FormatFast.FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre64 5 4608 80 rtT (Fv256.Amd64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre64 4 4608 80 rtT (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat 16 ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧ (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) := by
  exact ⟨⟨csTA, rfl, csTA_pre⟩,
    ⟨csNew, rfl, csNew_pre⟩,
    ⟨csW1, rfl, csW1_pre⟩,
    ⟨csW2, rfl, csW2_pre⟩,
    ⟨csSs, rfl, csSs_pre⟩,
    ⟨csSt, rfl, csSt_pre⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 1 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 1 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 2 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) data (BitVec.ofNat 64 2) 0x2000 0 (BitVec.ofNat 64 2) (strMem [49, 54] 0x2000), rfl, by rw [fb16 ch hch]; exact wr_pre 7340032 data [49, 54] (by decide) (by decide)⟩,
    ⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint")) 0 (BitVec.ofNat 64 (2 ^ 40 + 56)) data 1 1 m_fp, rfl, fp_pre _ data⟩,
    ⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format")) 0x2000 data tab 0 ch m_bf16, rfl, bf_pre16 _ tab data ch⟩⟩

theorem csAll0 (tab data ch : BitVec 64) (hch : ch.toNat % 2 ^ 32 ≠ 120) :
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Amd64.FormatCS.TypeAssertSite R0 Hw s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre64 rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre64 rtT 4096 Hw stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 1 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 1 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 2 4608 80 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 7340032 ∧ ICallPre64 4 4608 80 rtT (Fv256.FormatFast.FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre64 5 4608 80 rtT (Fv256.Amd64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre64 4 4608 80 rtT (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat 0 ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧ (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) := by
  exact ⟨⟨csTA, rfl, csTA_pre⟩,
    ⟨csNew, rfl, csNew_pre⟩,
    ⟨csW1, rfl, csW1_pre⟩,
    ⟨csW2, rfl, csW2_pre⟩,
    ⟨csSs, rfl, csSs_pre⟩,
    ⟨csSt, rfl, csSt_pre⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 1 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 1 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) 0 0 0 0 0 flatMem, rfl, ic_true 7340032 2 (by omega) (by omega)⟩,
    ⟨callSt64At (BitVec.ofNat 64 7340032) data (BitVec.ofNat 64 1) 0x2000 0 (BitVec.ofNat 64 1) (strMem [48] 0x2000), rfl, by rw [fb0 ch hch]; exact wr_pre 7340032 data [48] (by decide) (by decide)⟩,
    ⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint")) 0 (BitVec.ofNat 64 (2 ^ 40 + 56)) data 1 1 m_fp, rfl, fp_pre _ data⟩,
    ⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format")) 0x2000 data tab 0 ch m_bf0, rfl, bf_pre0 _ tab data ch⟩⟩

end Fv256.Amd64.FormatCS
