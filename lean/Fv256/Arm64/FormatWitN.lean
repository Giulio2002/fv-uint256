import Extracted
import Fv256.Arm64.FormatCS
import Fv256.Arm64.FormatWitB

/-!
# Format witness, part N: the nil receiver (`z = 0`) call state (arm64)

The `AsHasher` environment (`IfaceModel.R0`, `wmem`, the type-assertion descriptor `descA`), `tab = 0` (a nil `fmt.State`: the writer is nil),
the extracted data (the `"<nil>"` literal and its header) loaded read-only.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.Arm64.FormatTransfer Fv256.Arm64.FormatWitA Fv256.Arm64.FormatWitB Fv256.E Fv256.FormatFastA64
open Janus.Spec.Type Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Fv256.Arm64.FormatNil

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Arm64.FormatWitN

def tblN : List (Nat × Nat) :=
  [(descA + 1, 0x04), (descA + 2, 0x01), (descA + 9, 0x01), (descA + 10, 0x01), (descA + 16, 1)] ++ wtable

def bytesN (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((tblN.lookup a).getD 0)

def memN : Memory := ⟨bytesN, wmem.regions ++ [⟨descA - descA % 4096, 0x1000, true⟩] ++ dregs⟩

def s0N : State :=
  { regs := fun i => if i = 3 then chV else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := memN }

theorem setupN : CallSetup (linked.withExit ret) Extracted.entry [0, 0, 0, chV] s0N :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0N] at h ⊢ <;> omega⟩

theorem env : Env0 memN g := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  unfold Desc; decide +kernel

theorem desc_ok : TADescOK R0 memN descA := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by simp only [R0_isInter, taInter]; decide +kernel, ?_⟩
  show TACacheOK R0 memN (memN.readLE descA 8) (taInter memN descA)
  rw [show memN.readLE descA 8 = TAC by decide +kernel]
  exact TACacheOK.empty (by decide +kernel) (by decide +kernel) (inPriv (by decide +kernel) (by decide +kernel)) (by decide +kernel) (by decide +kernel)

theorem dataLoadedN : Extracted.program.DataLoaded memN := by
  unfold Program.DataLoaded
  decide +kernel


theorem preCommonN : PreCommon rtT stackN s0N := by
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  simp only [rtT, hA, hB, outside_cons, outside_nil, and_true]; decide +kernel

theorem preN : PreF R0 Hw R2 rtT stackN 0x400 amA amA amA amA 0 0 0 0 s0N := by
  refine ⟨preRt, preCommonN, fun _ => ⟨?_, fun h => absurd h (by decide)⟩, fun h => absurd h (by decide)⟩
  refine ⟨⟨env (g := s0N.regs 28), ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩, desc_ok, ?_, fun h => absurd h (by decide),
    dataLoadedN, ?_, ?_⟩
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · unfold Janus.Spec.Disjoint; decide +kernel
  · simp only [R0_priv, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [outside_cons, outside_nil, and_true, R0_depth]; decide +kernel
  · simp only [NilFLE, NilFL, TAFL, PFL, R0_priv, R0_depth, rtT, hA, hB, outside_append, outside_cons, outside_nil, and_true]; decide +kernel
  · simp only [NilFLE, NilFL, TAFL, PFL, R0_priv, R0_depth, rtT, hA, hB, outside_append, outside_cons, outside_nil, and_true]; decide +kernel


open Janus.Contracts.IfaceModel Janus.Spec.Type in
theorem nil_core : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (Fv256.Arm64.FormatNil.FpArg data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt 4608 0x400 fa fa fa fa 0 z tab data s ) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.FormatSpec.fastBytes 0 (ch.toNat % 2 ^ 32))) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (Fv256.Arm64.FormatNil.FpArg data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c) := by
  refine ⟨implAll, R0, Hw, R2, rtT, amA, R0z, R0z, 0, 0, 0, chV, ret, s0N,
    ⟨implOK, Janus.Contracts.IfaceModel.R0_laws, by rw [addr_ta]; exact model_ta, by rw [addr_new]; exact model_new, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2, model1, model2, by decide⟩,
    ⟨stub_gen amA (Or.inl rfl) _ _ _ _ _ _ (fun s b L h => h), stub_gen amA (Or.inl rfl) _ _ _ _ _ _ (fun s b L h => h), stub_gen amA (Or.inl rfl) _ _ _ _ _ _ (fun s b L h => h), stub_gen amA (Or.inl rfl) _ _ _ _ _ _ (fun _ => trivial), by rw [addr_fp]; exact stub_gen fpAddr (Or.inr (Or.inl rfl)) _ _ _ _ _ _ (fun _ => trivial), by rw [addr_bf]; exact stub_gen bfAddr (Or.inr (Or.inr rfl)) _ _ _ _ _ _ (fun _ => trivial), by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setupN, preN⟩, Fv256.Arm64.FormatCS.csAll0 0 0 chV rfl⟩

end Fv256.Arm64.FormatWitN
