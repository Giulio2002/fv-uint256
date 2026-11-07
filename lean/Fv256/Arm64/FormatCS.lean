import Extracted
import Fv256.Arm64.FormatWitA
import Fv256.Arm64.FormatNil
import Fv256.Arm64.FormatInhabit
import Fv256.Arm64.CallSites.Base

/-!
# `Format` (arm64): the call-site states of the twelve contract hypotheses (U-WITNESS-CALLSITE)

One universal environment `memU` / `sU` (the `IfaceModel.R0` metadata, the toy allocator's heap and bump word, the two string-runtime blocks, the
extracted data, a stack at `[0x40000, 0x50000)`, the goroutine at `0x50000`) serves the runtime stubs (`runtime.typeAssert`, `newobject`,
`gcWriteBarrier1/2`, `slicebytetostring`, `stringtoslicebyte`); the indirect calls (`ICallPre`) use the flat memory of `Fv256.Inhab`.
Each lemma is the conjunct `∃ s_c, s_c.pc = entry ∧ pre s_c` of the three witnesses (`FormatWitB`, `FormatWitG`, `FormatWitN`), at `z = 16` (fast and big paths) or `z = 0` (nil).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Toy
open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Janus.Spec.Type
open Fv256.Arm64.FormatWitA Fv256.Arm64.CallSites Fv256.Inhab

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Arm64.FormatCS

/-- the precondition of `runtime.typeAssert` as one conjunct (the contract's own `pre`) -/
@[reducible] def TypeAssertSite (R : IfaceModel) (H : RtReady) (s : State) : Prop :=
  RTPre R 2 s ∧ TADescOK R s.mem (s.regs 0).toNat ∧
      (s.regs 1).toNat ≠ 0 ∧
      ((s.regs 1).toNat ≠ 0 → R.IsType (s.regs 1).toNat ∧
        (taCanFail s.mem (s.regs 0).toNat = true ∨
          (R.itab (taInter s.mem (s.regs 0).toNat) (s.regs 1).toNat).isSome)) ∧
      Ready H R.priv [(s.regs 0).toNat, (s.regs 1).toNat] s

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
  { regs := fun i => if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 wret else 0,
    sp := BitVec.ofNat 64 wsp, pc := 0, flags := ⟨false, false, false, false⟩, mem := memU }

theorem envU (g : W64) : Env0 memU g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem descU : TADescOK R0 memU DTA := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by simp only [R0_isInter, taInter]; decide +kernel, ?_⟩
  show TACacheOK R0 memU (memU.readLE DTA 8) (taInter memU DTA)
  rw [show memU.readLE DTA 8 = TAC by decide +kernel]
  exact TACacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem rtpreU (s : State) (hm : s.mem = memU) (h28 : s.regs 28 = BitVec.ofNat 64 wg) (h30 : s.regs 30 = BitVec.ofNat 64 wret)
    (hsp : s.sp = BitVec.ofNat 64 wsp) (n : Nat) (hn : n ≤ 3) : RTPre R0 n s := by
  have hw : memU.accessible (wsp - 64) (64 + 8 + 8 * 3) true = true := by decide +kernel
  refine ⟨hm ▸ envU (s.regs 28), ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, by decide, ?_, ?_⟩, ?_⟩
  · simp only [regG, stackguard0Offset, h28]; decide
  · simp only [regG, stackguard0Offset, h28, hm]; decide +kernel
  · simp only [stackguard0, regG, stackguard0Offset, h28, hm, hsp, R0_depth]; decide +kernel
  · simp only [h30]; decide
  · simp only [h30]; decide
  · simp only [hsp]; decide
  · simp only [hsp, R0_depth]; decide
  · simp only [hsp]; simp [wsp]; omega
  · simp only [hsp, hm, R0_depth, BitVec.toNat_ofNat]
    exact Memory.accessible_mono _ hw (by simp [wsp]) (by simp [wsp]; omega)
  · simp only [hsp, R0_depth, R0_priv, outside_cons, outside_nil, and_true, BitVec.toNat_ofNat]
    simp [wsp]

theorem rt_eq : R2.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem inv0U : R2.inv 0x400 [] (sU.regs 28).toNat (view R2.rt [] sU.mem) := by
  have hbump : memU.readLE BUMP 8 = HEAP := by decide +kernel
  refine toyInv_init (m := memU) (g := (sU.regs 28).toNat) (by decide) hbump (fun i hi hi' => ?_) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
  have hl : tblU.lookup i = none := by
    simp only [tblU, wtable, List.lookup, BUMP, TD, ID, TAB, DTA, DIS, VAL]
    repeat (rw [if_neg (by omega)])
    rfl
  rw [hl]; rfl

/-! ### the runtime stubs -/

def csTA0 : State := { sU with regs := fun i => if i = 0 then BitVec.ofNat 64 DTA else if i = 1 then BitVec.ofNat 64 TD else sU.regs i }
def csTA : State := { csTA0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") }

set_option maxRecDepth 100000 in
theorem csTA_pre : TypeAssertSite R0 Hw csTA := by
  refine ⟨rtpreU csTA rfl rfl rfl rfl 2 (by decide), ?_, by decide, fun _ => ⟨Or.inl rfl, Or.inl (by decide +kernel)⟩, ?_⟩
  · exact descU
  · show Hw [csTA.regs 0 |>.toNat, csTA.regs 1 |>.toNat] _ _ (rtView R0.priv csTA.mem)
    simp only [Hw]
    refine ⟨Or.inr ⟨_, _, rfl⟩, ?_, ?_⟩ <;> rw [Janus.Arm64.Memory.accessible_congr rfl] <;> decide +kernel

def csNew0 : State := { sU with regs := fun i => if i = 0 then BitVec.ofNat 64 Fv256.Arm64.IntoBig.bigType else sU.regs i }
def csNew : State := { csNew0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csW1 : State := { sU with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { sU with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨callOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    typeOK_of (by decide +kernel) (by decide +kernel), by decide +kernel⟩,
    ⟨guardOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel), by simp only [calleeStack, outside_cons, outside_nil]; decide +kernel⟩,
    ?_, inv0U, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl (by decide)⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide +kernel)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 := by
  refine ⟨callOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0U, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide +kernel

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 := by
  refine ⟨callOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0U, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide +kernel

/-! ### the string runtime: `slicebytetostring(nil, VAL, 2)` and `stringtoslicebyte(nil, VAL, 2)` -/

def csStr0 : State := { sU with regs := fun i => if i = 1 then BitVec.ofNat 64 VAL else if i = 2 then 2 else sU.regs i }
def csSs : State := { csStr0 with pc := BitVec.ofNat 64 ssAddr }
def csSt : State := { csStr0 with pc := BitVec.ofNat 64 stAddr }

theorem csStr_ready (s : State) (hs : s.regs 0 = 0 ∧ s.regs 1 = BitVec.ofNat 64 VAL ∧ s.regs 2 = 2) (hm : s.mem = memU) :
    Ready Hw rtT (argWords s 3) s := by
  obtain ⟨h0, h1, h2⟩ := hs
  have e : argWords s 3 = [0, VAL, 2] := by
    simp [argWords, wordsFrom, arg, h0, h1, h2, VAL]
  show Hw (argWords s 3) _ _ (rtView rtT s.mem)
  rw [e]
  simp only [Hw]
  refine ⟨Or.inl (Or.inl ⟨_, rfl⟩), ?_, ?_⟩ <;> rw [rtView_acc, hm] <;> decide +kernel

set_option maxRecDepth 100000 in
theorem csSs_pre : RtPre rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSs := by
  refine ⟨callOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide +kernel), by decide +kernel, fun h => absurd (by decide +kernel) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide +kernel
  · exact csStr_ready csSs ⟨rfl, rfl, rfl⟩ rfl

set_option maxRecDepth 100000 in
theorem csSt_pre : RtPre rtT 4096 Hw stringtoslicebyteSpec csSt := by
  refine ⟨callOK_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide +kernel), by decide +kernel, fun h => absurd (by decide +kernel) h⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide +kernel
  · exact csStr_ready csSt ⟨rfl, rfl, rfl⟩ rfl

/-! ### the indirect calls (flat memory) -/

/-- an indirect-call state: `Fv256.Inhab.callSt` with the program counter at the callee's entry -/
def csI (pc : Nat) (r0 r1 r2 r3 r4 : W64) (m : Memory) : State := { callSt r0 r1 r2 r3 r4 m with pc := BitVec.ofNat 64 pc }

@[simp] theorem csI_r0 (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).regs 0 = a := by simp [csI]
@[simp] theorem csI_r1 (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).regs 1 = b := by simp [csI]
@[simp] theorem csI_r2 (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).regs 2 = c := by simp [csI]
@[simp] theorem csI_r3 (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).regs 3 = d := by simp [csI]
@[simp] theorem csI_r4 (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).regs 4 = e := by simp [csI]
@[simp] theorem csI_sp (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).sp = BitVec.ofNat 64 (2 ^ 40) := rfl
@[simp] theorem csI_mem (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).mem = m := rfl
@[simp] theorem csI_pc (pc : Nat) (a b c d e : W64) (m : Memory) : (csI pc a b c d e m).pc = BitVec.ofNat 64 pc := rfl

theorem csI_pre {pc : Nat} {r0 r1 r2 r3 r4 : W64} {m : Memory} (hm : m.regions = [⟨0, 2 ^ 48, true⟩]) {nargs stack above : Nat}
    (rt : List (Nat × Nat)) (hrt : Outside (2 ^ 40 - 8) (above + 8) rt)
    (h8 : 8 ≤ stack) (hs : stack ≤ 2 ^ 40) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ above) {P : State → Prop}
    (hP : P (csI pc r0 r1 r2 r3 r4 m)) : ICallPre nargs stack above rt P (csI pc r0 r1 r2 r3 r4 m) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, h8, ?_, accessible_flat _ hm _ _ _ ?_⟩, hab, ?_, hP⟩ <;>
    simp [csI, callSt, hsp, hrt] <;> first | omega | exact hrt | skip

theorem outside_far (above : Nat) (h : above ≤ 200) : Outside (2 ^ 40 - 8) (above + 8) rtT := by
  simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]
  omega

/-- the `Write` call: the slice holds `bs` -/
theorem wr_pre (pc : Nat) (data : BitVec 64) (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) (hl : bs.length ≤ 2 ^ 20) :
    ICallPre 4 4608 120 rtT (Fv256.FormatFastA64.FastWP data bs)
      (csI pc data 0x2000 (BitVec.ofNat 64 bs.length) (BitVec.ofNat 64 bs.length) 0 (strMem bs 0x2000)) := by
  have hm : (strMem bs 0x2000).regions = [⟨0, 2 ^ 48, true⟩] := rfl
  refine csI_pre hm rtT (outside_far 120 (by omega)) (by omega) (by omega) (by omega) (by omega) ?_
  have hlen : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨rfl, ?_, ?_⟩
  · simp only [csI_r1, csI_r2, csI_mem, hlen]
    have := strOut_strMem bs hb 0x2000 (by omega)
    simpa using this
  · simp only [csI_r2, csI_r3, hlen]; exact Nat.le_refl _

theorem fb16 (ch : BitVec 64) (hch : ch = 100) : Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32) = [49, 54] := by
  subst hch
  have h1 : Fv256.E.decBytes 16 = [49, 54] := by
    rw [Fv256.E.decBytes_ge 16 (by omega)]
    simp [Fv256.E.decBytes_lt 1 (by omega), Fv256.E.decBytes_lt 6 (by omega)]
  simp [Fv256.FormatSpec.fastBytes, h1]

theorem fb0 (ch : BitVec 64) (hch : ch = 100) : Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32) = [48] := by
  subst hch
  simp [Fv256.FormatSpec.fastBytes, Fv256.E.decBytes]

open Fv256.Arm64.FormatNil in
/-- the flat memory of the `Fprint` call: the string literal, its header and descriptor word as `FpArg` asks -/
def m_fp : Memory := ((((strMem Fv256.FormatSpec.nilText litA).writeLE (2 ^ 40 + 56) 8 strTyA).writeLE (2 ^ 40 + 64) 8 hdrA).writeLE
    hdrA 8 litA).writeLE (hdrA + 8) 8 5

open Fv256.Arm64.FormatNil in
/-- `fmt.Fprint(w, "<nil>")`: the property `FpArg data` over the extraction's addresses -/
theorem fp_pre (pc : Nat) (data : BitVec 64) :
    ICallPre 5 4608 80 rtT (FpArg data) (csI pc data (BitVec.ofNat 64 (2 ^ 40 + 56)) 1 1 m_fp) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40 + 56)).toNat = 2 ^ 40 + 56 := by simp
  have hsp' : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  have h1 : strTyA < 2 ^ 64 := by decide
  have h2 : hdrA < 2 ^ 64 := by decide
  have h3 : litA < 2 ^ 64 := by decide
  have hd1 : litA + 5 ≤ 2 ^ 40 := by decide
  have hd2 : hdrA + 16 ≤ 2 ^ 40 := by decide
  have hd3 : litA + 5 ≤ hdrA ∨ hdrA + 16 ≤ litA := by decide
  have hm : m_fp.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_fp, strMem]
  refine csI_pre hm rtT (outside_far 80 (by omega)) (by omega) (by omega) (by omega) (by omega) ?_
  simp only [FpArg, csI_r1, csI_r2, csI_r3, csI_r4, csI_sp, csI_mem, hsp, hsp']
  refine ⟨trivial, rfl, rfl, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [m_fp, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h1)
  · simp (disch := omega) only [m_fp, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h2)
  · simp (disch := omega) only [m_fp, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h3)
  · simp (disch := omega) only [m_fp, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  · have := strOut_strMem Fv256.FormatSpec.nilText (by simp [Fv256.FormatSpec.nilText]) litA (by simp [Fv256.FormatSpec.nilText]; omega)
    simp only [m_fp]
    refine strOut_writeLE (strOut_writeLE (strOut_writeLE (strOut_writeLE this _ _ _ ?_) _ _ _ ?_) _ _ _ ?_) _ _ _ ?_ <;>
      simp [Fv256.FormatSpec.nilText] <;> omega

/-- the receiver `P = 0x2000` of `(*big.Int).Format` holds `zv`: `len = 0` (`zv = 0`) or one limb (`zv = 16`) -/
def m_bf0 : Memory := flatMem.writeLE (0x2000 + 24) 8 4
def m_bf16 : Memory := (((flatMem.writeLE (0x2000 + 24) 8 4).writeLE (0x2000 + 16) 8 1).writeLE (0x2000 + 8) 8 0x3000).writeLE 0x3000 8 16

theorem bf_pre0 (pc : Nat) (tab data ch : BitVec 64) :
    ICallPre 4 4608 120 rtT (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧
      sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) (csI pc 0x2000 tab data ch 0 m_bf0) := by
  have hm : m_bf0.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_bf0, flatMem]
  refine csI_pre hm rtT (outside_far 120 (by omega)) (by omega) (by omega) (by omega) (by omega) ?_
  refine ⟨0x2000, by simp, ?_, by simp, by simp, by simp⟩
  simp only [csI_mem]
  refine ⟨0, 0, 4, ?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, by omega, by omega, Or.inl rfl, rfl⟩
  · simp [m_bf0]; exact accessible_flat flatMem rfl _ _ _ (by omega)
  · simp (disch := omega) only [m_bf0, Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf0, Memory.readLE_writeLE_self]
  · simp [m_bf0]; exact accessible_flat flatMem rfl _ _ _ (by omega)

theorem bf_pre16 (pc : Nat) (tab data ch : BitVec 64) :
    ICallPre 4 4608 120 rtT (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧
      sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) (csI pc 0x2000 tab data ch 0 m_bf16) := by
  have hm : m_bf16.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m_bf16, flatMem]
  refine csI_pre hm rtT (outside_far 120 (by omega)) (by omega) (by omega) (by omega) (by omega) ?_
  refine ⟨0x2000, by simp, ?_, by simp, by simp, by simp⟩
  simp only [csI_mem]
  refine ⟨0x3000, 1, 4, ?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, by omega, by omega, Or.inr ?_, ?_⟩
  · simp [m_bf16]; exact accessible_flat flatMem rfl _ _ _ (by omega)
  · simp (disch := omega) only [m_bf16, Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m_bf16, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    sorry
  · simp (disch := omega) only [m_bf16, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
    sorry
  · simp (disch := omega) only [m_bf16, Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
  · simp [m_bf16]; exact accessible_flat flatMem rfl _ _ _ (by omega)
  · simp (disch := omega) only [m_bf16, Memory.readLE_writeLE_self]
    sorry
  · simp [Fv256.C.bigAbs]
    sorry

theorem ic_true (pc nargs : Nat) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ 120) :
    ICallPre nargs 4608 120 rtT (fun _ => True) (csI pc 0 0 0 0 0 flatMem) :=
  csI_pre (m := flatMem) rfl rtT (outside_far 120 (by omega)) (by omega) (by omega) hn hab trivial

open Janus.Contracts.IfaceModel in

theorem ic_true (pc nargs : Nat) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ 120) :
    ICallPre nargs 4608 120 rtT (fun _ => True) (csI pc 0 0 0 0 0 flatMem) :=
  csI_pre (m := flatMem) rfl rtT (outside_far 120 (by omega)) (by omega) (by omega) hn hab trivial

open Janus.Contracts.IfaceModel in
-- AGGREGATE-BEGIN

theorem csAll16 (tab data ch : BitVec 64) (hch : ch = 100) :
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R0 Hw s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rtT 4096 Hw stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 1 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 1 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 2 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 4 4608 120 rtT (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rtT (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rtT (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) := by
  exact ⟨⟨csTA, rfl, csTA_pre⟩,
    ⟨csNew, rfl, csNew_pre⟩,
    ⟨csW1, rfl, csW1_pre⟩,
    ⟨csW2, rfl, csW2_pre⟩,
    ⟨csSs, rfl, csSs_pre⟩,
    ⟨csSt, rfl, csSt_pre⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 1 (by omega) (by omega)⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 1 (by omega) (by omega)⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 2 (by omega) (by omega)⟩,
    ⟨csI amA data 0x2000 (BitVec.ofNat 64 2) (BitVec.ofNat 64 2) 0 (strMem [49, 54] 0x2000), rfl, by rw [fb16 ch hch]; exact wr_pre amA data [49, 54] (by decide) (by decide)⟩,
    ⟨csI (Extracted.program.contractAddr "fmt.Fprint") data (BitVec.ofNat 64 (2 ^ 40 + 56)) 1 1 0 m_fp, rfl, fp_pre _ data⟩,
    ⟨csI (Extracted.program.contractAddr "math/big.(*Int).Format") 0x2000 tab data ch 0 m_bf16, rfl, bf_pre16 _ tab data ch⟩⟩

theorem csAll0 (tab data ch : BitVec 64) (hch : ch = 100) :
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R0 Hw s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rtT 4096 Hw stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 1 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 1 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 2 4608 120 rtT (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 amA ∧ ICallPre 4 4608 120 rtT (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rtT (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rtT (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) := by
  exact ⟨⟨csTA, rfl, csTA_pre⟩,
    ⟨csNew, rfl, csNew_pre⟩,
    ⟨csW1, rfl, csW1_pre⟩,
    ⟨csW2, rfl, csW2_pre⟩,
    ⟨csSs, rfl, csSs_pre⟩,
    ⟨csSt, rfl, csSt_pre⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 1 (by omega) (by omega)⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 1 (by omega) (by omega)⟩,
    ⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA 2 (by omega) (by omega)⟩,
    ⟨csI amA data 0x2000 (BitVec.ofNat 64 1) (BitVec.ofNat 64 1) 0 (strMem [48] 0x2000), rfl, by rw [fb0 ch hch]; exact wr_pre amA data [48] (by decide) (by decide)⟩,
    ⟨csI (Extracted.program.contractAddr "fmt.Fprint") data (BitVec.ofNat 64 (2 ^ 40 + 56)) 1 1 0 m_fp, rfl, fp_pre _ data⟩,
    ⟨csI (Extracted.program.contractAddr "math/big.(*Int).Format") 0x2000 tab data ch 0 m_bf0, rfl, bf_pre0 _ tab data ch⟩⟩

end Fv256.Arm64.FormatCS
