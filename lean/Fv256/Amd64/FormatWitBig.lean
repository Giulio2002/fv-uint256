import Extracted
import Fv256.Amd64.FormatWitA
import Fv256.Amd64.FormatBigDefs

/-!
# Format witness, big path: the call state with verb `q` (amd64)

`z = 16` (decimal `16`, hexadecimal `0x10`), verb `d`, all queries answered plain by the trivial callees.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.Amd64.FormatTransfer Fv256.Amd64.FormatWitA Fv256.E Fv256.Amd64.FormatBig

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Amd64.FormatWitBig

open Janus.Contracts.Toy


def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zA : Nat := 0x310000
def tabA : Nat := 0x320000
def stackN : Nat := 4608

def dsegs : List DataSegment := Extracted.data
def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zA then 16 else
  if a = tabA + 0x18 + 2 ∨ a = tabA + 0x20 + 2 ∨ a = tabA + 0x28 + 2 ∨ a = tabA + 0x30 + 2 then 0x70 else
  if a = BUMP + 3 then 0x10 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def mem0 : Memory :=
  ⟨bytes, [⟨sp0 - 4688, 4736 + 16, true⟩, ⟨g0, 0x100, false⟩, ⟨zA, 32, false⟩, ⟨tabA, 0x40, false⟩,
    ⟨hA, 8, true⟩, ⟨hB, 8, true⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩, ⟨Fv256.Amd64.IntoBig.flagAddr, 8, false⟩] ++ dregs⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA
def tabV : BitVec 64 := BitVec.ofNat 64 tabA
def dataV : BitVec 64 := 0
def chV : BitVec 64 := 113

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zV else if i = 3 then tabV else if i = 1 then dataV else if i = 7 then chV
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV, tabV, dataV, chV] s0 := by
  refine ⟨rfl, by decide, rfl, by decide, ?_, rfl⟩
  intro i h
  have : i < 4 := by simpa using h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem preRt : PreRt rtT := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; simp only [rtT, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
  · have : ∀ d ∈ Extracted.data, (d.base + d.bytes.length ≤ hA ∨ hA + 8 ≤ d.base) ∧ (d.base + d.bytes.length ≤ hB ∨ hB + 8 ≤ d.base) := by
      decide
    intro d hd
    have := this d hd
    simp only [rtT, outside_cons, outside_nil, and_true]
    exact this
  · simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide

theorem preCommon : PreCommon rtT stackN s0 := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, by decide, by decide, by decide,
    by decide, ?_⟩
  simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide

theorem preFastE : PreFastE rtT stackN zV tabV dataV amA amA amA amA s0 := by
  have hc : CodePtrOK64 amA := by unfold CodePtrOK64 amA; decide
  refine ⟨hc, hc, hc, hc, by decide, by decide, by decide, by decide, by decide, by decide, ?_,
    by decide, by decide, by decide, ?_, by decide⟩
  · simp only [tabV, tabA, rtT, hA, hB, outside_cons, outside_nil, and_true]; decide
  · simp only [zV, zA, rtT, hA, hB, outside_cons, outside_nil, and_true]; decide

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem hzv : s0.mem.readLE zV.toNat 32 = 16 := by
  unfold s0 zV zA; decide

theorem hdb : decBytes 16 = [49, 54] := by
  rw [decBytes_ge 16 (by omega)]
  simp [decBytes_lt 1 (by omega), decBytes_lt 6 (by omega)]

theorem hexdig16 {n : Nat} (h : Fv256.C.hexDigits 16 n) : n = 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases h3 with h3 | h3
  · subst h3; exact absurd h2 (by decide)
  · by_cases hn : n ≤ 2
    · rcases (by omega : n = 1 ∨ n = 2) with rfl | rfl
      · exact absurd h2 (by decide)
      · rfl
    · exfalso
      have : 16 ^ 2 ≤ 16 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h256 : (16:Nat) ^ 2 = 256 := by decide
      omega

theorem hw_of {a : List Nat} (ha : (∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, p, 4])) (g sp : Nat) {X : List (Nat × Nat)}
    {M : Memory} (hMF : MemFrame s0.mem M X) (hsp : sp + 8 ≤ hA) : Hw a g sp (rtView rtT M) := by
  refine ⟨ha, ?_, ?_, Or.inl (by omega), Or.inl (by simp only [hA, hB] at *; omega)⟩
  · rw [rtView_acc, hMF.accessible]; decide
  · rw [rtView_acc, hMF.accessible]; decide

theorem hypsH : HypsH Hw rtT zV (sp0 - 72) g0 s0.mem (FLE rtT sp0 stackN) := by
  have hz := hzv
  refine ⟨fun M hM h => absurd h (by rw [hz]; decide), fun M hM h _ => absurd h (by rw [hz]; decide), ?_, ?_, ?_⟩
  · intro M p l hM hSO hDA
    rw [hz, hdb] at hSO
    have hl : l = 2 := by have := hSO.1; simpa using this
    subst hl
    exact hw_of (Or.inl ⟨p, rfl⟩) _ _ hM (by simp only [hA, sp0]; omega)
  · intro M hM n hn
    have := hexdig16 (by rw [hz] at hn; exact hn)
    subst this
    exact hw_of (Or.inr ⟨_, rfl⟩) _ _ hM (by simp only [hA, sp0]; omega)
  · intro M p l n hM hn hSO hIn
    have := hexdig16 (by rw [hz] at hn; exact hn)
    subst this
    rw [hz] at hSO
    have hl : l = 4 := by have := hSO.1; simpa [Fv256.C.hexStrBytes] using this
    subst hl
    exact hw_of (Or.inl ⟨p + 2, rfl⟩) _ _ hM (by simp only [hA, sp0]; omega)

theorem preFastX : PreFastX Hw rtT stackN zV s0 := by
  refine ⟨dataLoaded, by decide, by decide, by decide, ?_, by decide, hypsH⟩
  simp only [s0, g0, rtT, hA, hB, outside_cons, outside_nil, and_true]; decide

theorem find_none (a : Nat) (ha : 0x500000 ≤ a) :
    dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) = none := by
  rw [List.find?_eq_none]
  intro d hd
  have h2 : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
  have := h2 d hd
  simp only [Bool.not_eq_true, decide_eq_false_iff_not]
  omega

theorem inv0 : R2.inv 0x400 [] (s0.regs 14).toNat (view R2.rt [] s0.mem) := by
  have hbump : mem0.readLE BUMP 8 = HEAP := by decide
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) hbump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes i = 0
  have h1 : 0x10000000 ≤ i := by simp only [HEAP] at hi; omega
  unfold bytes
  rw [find_none i (by omega)]
  have e1 : ¬ i = sp0 + 2 := by simp only [sp0]; omega
  have e2 : ¬ i = zA := by simp only [zA]; omega
  have e3 : ¬ (i = tabA + 0x18 + 2 ∨ i = tabA + 0x20 + 2 ∨ i = tabA + 0x28 + 2 ∨ i = tabA + 0x30 + 2) := by simp only [tabA]; omega
  have e4 : ¬ i = BUMP + 3 := by simp only [BUMP]; omega
  rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4]

theorem rtb_eq : R2.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

open Fv256.Amd64.IntoBig Fv256.Amd64.FormatBig in
theorem preBig : PreBigE R2 0x400 zV s0 := by
  refine ⟨by decide, ?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩
  · rw [rtb_eq]; simp only [s0, g0, outside_cons, outside_nil, and_true, HEND, HEAP, HSIZE, BUMP, WBUF]; decide
  · rw [rtb_eq]; simp only [outside_cons, outside_nil, and_true, HEND, HEAP, HSIZE, BUMP, WBUF]; decide
  · rw [rtb_eq]; simp only [outside_cons, outside_nil, and_true, HEND, HEAP, HSIZE, BUMP, WBUF]; decide
  · rw [rtb_eq]; simp only [zV, zA, outside_cons, outside_nil, and_true, HEND, HEAP, HSIZE, BUMP, WBUF]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inr rfl⟩
  · rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)

open Janus.Contracts.IfaceSatAmd64 in
theorem pre : PreF R0 Hw R2 rtT stackN 0x400 amA amA amA amA 16 zV tabV dataV s0 := by
  refine ⟨preRt, preCommon, fun h => absurd h (by decide), fun _ => ⟨preFastE, preFastX, hzv, inv0, ?_, preBig⟩⟩
  show Outside _ _ (Janus.Contracts.Toy.toyRt [])
  simp only [Janus.Contracts.Toy.toyRt, List.map_nil, List.append_nil, s0, sp0, stackN, outside_cons, outside_nil, and_true,
    HEAP, HEND, HSIZE, BUMP, WBUF]
  decide

open Fv256.Amd64.FormatFast Fv256.FormatFast in
/-- with these answers (all queries plain) and the verb `q`, the code leaves the query chain for the big path: `NotPlain` holds -/
theorem bigPath_taken : NotPlain R0z R0z R0z dataV tabV chV amA amA (chV.toNat % 2 ^ 32) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
  refine ⟨0, ?_, by simp [chV], by simp [chV], by simp [chV], by simp [chV]⟩
  simp [PlainHist, WRes, PRes, FRes, R0z, fz, fx]
  exact ⟨0, 0, ⟨rfl, rfl⟩, rfl⟩

open Janus.Contracts.IfaceSatAmd64 Fv256.FormatFast Fv256.Amd64.FormatFast Janus.Spec.Type in
theorem nonvacuous_big_core : ∃ (impl : List Amd64.Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fW fP fF fWr stack b0 zv : Nat) (RW RP RF RWr RFp RBf : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    Fv256.Amd64.FormatWitA.pinT stack b0 zv fW fP fF fWr z tab data ch ret s rt ∧
    Amd64.ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.IfaceAmd64.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4568 ≤ stack ∧
    ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2) ∧
    ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2) ∧
    ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2) ∧
    ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes zv (ch.toNat % 2 ^ 32))) ∧
    ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (Fv256.Amd64.FormatNil.FpArg data) ∧
    ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => [])
      RBf (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat zv ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data s ∧
    z.toNat ≠ 0 ∧ NotPlain RW RP RF data tab ch fP fF (ch.toNat % 2 ^ 32) := by
  refine ⟨implAll, Janus.Contracts.IfaceModel.R0, Hw, R2, rtT, amA, amA, amA, amA, stackN, 0x400, 16, R0z, R0z, R0z, R0z, R0z, R0z, zV, tabV, dataV, chV, ret, s0,
    trivial, implOK, Janus.Contracts.IfaceModel.R0_laws, model_ta, model_new, model_wb1, model_wb2, model1, model2, by decide,
    stub_am _ _ _ _ _ _ (fun s b L h => h), stub_am _ _ _ _ _ _ (fun s b L h => h), stub_am _ _ _ _ _ _ (fun s b L h => h),
    stub_am _ _ _ _ _ _ (fun _ => trivial), stub_fp _ _ _ _ _ _ (fun _ => trivial), stub_bf _ _ _ _ _ _ (fun _ => trivial),
    by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setup, pre, by decide, bigPath_taken⟩

end Fv256.Amd64.FormatWitBig
