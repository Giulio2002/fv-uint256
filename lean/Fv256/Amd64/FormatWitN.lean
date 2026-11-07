import Extracted
import Fv256.Amd64.FormatWitB

/-!
# Format witness, part N: the nil receiver (`z = 0`) call state (amd64)

The `AsHasher` environment (`IfaceModel.R0`, `wmem`, the type-assertion descriptor `descA`), `tab = 0` (a nil `fmt.State`: the writer is nil),
the extracted data (the `"<nil>"` literal and its header) loaded read-only.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.Amd64.FormatTransfer Fv256.Amd64.FormatWitA Fv256.Amd64.FormatWitB Fv256.E
open Janus.Spec.Type Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64 Fv256.Amd64.FormatNil

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Amd64.FormatWitN

def tblN : List (Nat × Nat) :=
  [(wsp + 2, 0x20), (descA + 1, 0x04), (descA + 2, 0x01), (descA + 9, 0x01), (descA + 10, 0x01), (descA + 16, 1)] ++ wtable

def bytesN (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((tblN.lookup a).getD 0)

def memN : Memory := ⟨bytesN, wmem.regions ++ [⟨descA - descA % 4096, 0x1000, true⟩] ++ dregs⟩

def s0N : Amd64.State :=
  { regs := fun i => if i = 7 then chV else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0, mem := memN }

theorem setupN : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, chV] s0N := by
  refine ⟨rfl, by decide +kernel, rfl, by decide +kernel, ?_, rfl⟩
  intro i h
  have : i < 4 := by simpa using h
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl


theorem env : Env0 memN g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem desc_ok : TADescOK R0 memN descA := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by simp only [R0_isInter, taInter]; decide +kernel, ?_⟩
  show TACacheOK R0 memN (memN.readLE descA 8) (taInter memN descA)
  rw [show memN.readLE descA 8 = TAC by decide +kernel]
  exact TACacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem dataLoadedN : Extracted.program.DataLoaded memN := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem preCommonN : PreCommon rtT stackN s0N := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by unfold stackguard0 stackguard0Offset regG regSP; decide +kernel⟩, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide +kernel


theorem preN : PreF R0 Hw R2 rtT stackN 0x400 amA amA amA amA 0 0 0 0 s0N := by
  refine ⟨preRt, preCommonN, fun _ => ⟨?_, fun h => absurd h (by decide)⟩, fun h => absurd h (by decide)⟩
  refine ⟨⟨env (g := s0N.regs 14), ⟨by decide +kernel, by decide +kernel, by unfold stackguard0 stackguard0Offset regG regSP; decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩, desc_ok, ?_, fun h => absurd h (by decide),
    dataLoadedN, ?_, ?_⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · unfold Janus.Spec.Disjoint; decide +kernel
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [outside_cons, outside_nil, and_true, R0_depth]; decide +kernel
  · simp only [NilFLE, NilFL, TAFL, PFL, R0_priv, R0_depth, rtT, hA, hB, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [NilFLE, NilFL, TAFL, PFL, R0_priv, R0_depth, rtT, hA, hB, outside_append, outside_cons, outside_nil, and_true]; decide +kernel

open Janus.Contracts.IfaceSatAmd64 Fv256.FormatFast Fv256.Amd64.FormatFast Janus.Spec.Type in
theorem nil_core : ∃ (impl : List Amd64.Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fW fP fF fWr stack b0 zv : Nat) (RW RP RF RWr RFp RBf : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (Fv256.Amd64.FormatWitA.pinT stack b0 zv fW fP fF fWr z tab data ch ret s rt impl R H R2 RW RP RF RWr RFp RBf ∧
    Amd64.ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.IfaceAmd64.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2) ∧
    (RtContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4568 ≤ stack ∧
    ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2) ∧
    ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2) ∧
    ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)) ∧
    (ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes zv (ch.toNat % 2 ^ 32))) ∧
    ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (Fv256.Amd64.FormatNil.FpArg data) ∧
    ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => [])
      RBf (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat zv ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data s) := by
  refine ⟨implAll, Janus.Contracts.IfaceModel.R0, Hw, R2, rtT, amA, amA, amA, amA, stackN, 0x400, 0, R0z, R0z, R0z, R0z, R0z, R0z, 0, 0, 0, chV, ret, s0N,
    ⟨trivial, implOK, Janus.Contracts.IfaceModel.R0_laws, model_ta, model_new, model_wb1, model_wb2⟩, ⟨model1, model2, by decide,
    stub_am _ _ _ _ _ _ (fun s b L h => h), stub_am _ _ _ _ _ _ (fun s b L h => h), stub_am _ _ _ _ _ _ (fun s b L h => h)⟩, ⟨stub_am _ _ _ _ _ _ (fun _ => trivial), stub_fp _ _ _ _ _ _ (fun _ => trivial), stub_bf _ _ _ _ _ _ (fun _ => trivial),
    by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setupN, preN⟩⟩

end Fv256.Amd64.FormatWitN
