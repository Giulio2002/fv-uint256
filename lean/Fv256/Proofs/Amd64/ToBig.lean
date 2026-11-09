import Extracted
import Fv256.Proofs.Amd64.CallSites.Live
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Amd64.TB.IntoBigT

/-!
# `(*uint256.Int).ToBig() *big.Int` (amd64)

```go
func (z *Int) ToBig() *big.Int {
	if z == nil { return nil }
	var b *big.Int
	z.IntoBig(&b)
	return b
}
```
`IntoBig` is a second function of the same extraction (at `ToBig+0x60`). It is proved about its own code
(`(Extracted.program.onlySegments [IntoBig]).link impl`; the modules `Fv256.Amd64.TB.IntoBig*` are the `IntoBig`
proofs re-targeted mechanically at this extraction by `scripts/gen-tb-intobig-amd64.sh`) and used here as a callee
summary (`Ensures.toSummaryIn`). The runtime contracts are hypotheses about the program with no user code
(`Extracted.program.ofImpl impl`), moved up to the callee's and to the whole program.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

namespace Fv256.Amd64.ToBig

open Fv256.Amd64.IntoBig

/-- the callee's name -/
abbrev nmIB : String := "github.com/holiman/uint256.(*Int).IntoBig"
abbrev P0 (impl : List Amd64.Segment) : Amd64.Program := (Extracted.program.onlySegments [nmIB]).link impl

theorem hx_IB (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) :
    (P0 impl).fetch (P0 impl).exitAddr = none := by
  cases hf : (P0 impl).fetch (P0 impl).exitAddr with
  | none => rfl
  | some w =>
    obtain ⟨seg, hm, h1, h2⟩ := Program.fetchIn_index hf
    have hm' : seg ∈ Extracted.program.segments ++ impl := by
      rcases List.mem_append.1 hm with h | h
      · exact List.mem_append_left _ (List.mem_filter.1 h).1
      · exact List.mem_append_right _ h
    exfalso
    have e : (P0 impl).exitAddr = Extracted.program.exitAddr := rfl
    rw [e] at h1 h2
    exact (hI.2 seg hm' (Extracted.program.exitAddr - seg.base) (by omega)).2 (by omega)


/-- `Pre` with the nested facts about `*bp` dropped (they only matter when `*bp ≠ 0`; the call site has `*bp = 0`). -/
def PreC (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4128) 4152 R.rt ∧ Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4152 ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ b ∧
    Buffer s bp 8 true ∧ Outside bp.toNat 8 R.rt ∧ Janus.Spec.Disjoint bp.toNat 8 ((s.regs 4).toNat - 4128) 4152 ∧
    (z.toNat ≠ 0 →
      Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧ Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4128) 4152 ∧
      Janus.Spec.Disjoint z.toNat 32 bp.toNat 8)

theorem pre_mono {R : RtInv} {b : Nat} {z bp : BitVec 64} {s : State} (h : PreC R b z bp s)
    (hx : Apart bp.toNat 8 ((s.regs 14).toNat + 16) 8) (h0 : s.mem.readLE bp.toNat 8 = 0) :
    Pre R b z bp s ∧ PreX z bp s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ := h
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, fun hz => ?_⟩, hx, fun _ hne => absurd h0 hne⟩
  obtain ⟨b1, b2, b3, b4⟩ := a20 hz
  exact ⟨b1, b2, b3, b4, fun hne => absurd h0 hne⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 4168 ∧ StackWritable s 4168 8 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4168) 4176 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4168) 4168 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
        blockSize 32 false + blockSize 32 true ≤ b ∧
        (z.toNat ≠ 0 → Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧
          Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4168) 4168))
      (fun s s' => (z.toNat = 0 → s'.regs 0 = 0) ∧
        (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)])) := by
  intro ret hret s hs ⟨hg, ⟨hb', ha, hw⟩, hal, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4, hinv, hbud, hz⟩
  have hcn := codeIn_ofImpl_restrict_of_apart64 hI [nmIB]
  have hnew' := NewobjectLiveContract64.of_codeIn hcn hnew
  have hwb1' := WbLiveContract64.of_codeIn hcn hwb1
  have hwb2' := WbLiveContract64.of_codeIn hcn hwb2
  have S := Ensures.toSummaryIn
    (Fv256.Amd64.IntoBig.correctness impl R b z (s.regs 4 - 16#64) hnew' hwb1' hwb2')
    (hx_IB impl hI) (by show 2 ≤ 9; decide) (codeIn_restrict_of_apart64 hI [nmIB])
  have S' := Summary.mono S
    (pre' := fun sc => RetAddr (P0 impl) (sc.mem.readLE (sc.regs regSP).toNat 8) ∧ sc.xmm xmmZero = 0 ∧
      ArgsFrom64 sc 0 [z, s.regs 4 - 16#64] ∧ sc.df = false ∧
      (PreC R b z (s.regs 4 - 16#64) sc ∧ Apart (s.regs 4 - 16#64).toNat 8 ((sc.regs 14).toNat + 16) 8 ∧
        sc.mem.readLE (s.regs 4 - 16#64).toNat 8 = 0))
    (fun sc ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, pre_mono h5 h6 h7⟩) (fun s s' _ h => h)
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset, Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hb' ha hw hal hout hga hgr hz
  janus_eval_nat h_b : bigType
  janus_eval_nat h_a : arrType
  janus_eval_nat h_f : flagAddr
  rw [h_b] at hty1 hok1
  rw [h_a] at hty2 hok2
  rw [h_f] at hflag
  by_cases hz0 : z.toNat = 0
  · janus64_data hd [hw]
    janus64_run
    refine ⟨fun h => absurd h (by simp), ?_⟩
    exact (MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 4168, (s.regs 4).toNat), by simp, by omega, by omega⟩
  · obtain ⟨hzb, hzo, hzd⟩ := hz hz0
    obtain ⟨hz48, hzacc⟩ := hzb
    simp only [Janus.Spec.Disjoint] at hzd
    janus64_data hd [hw]
    janus64_run until [Extracted.entry + 0x26] calls [S']
    rename_i hbr0 hpc' hpost h4 h5 h14 hx15
    obtain ⟨-, hbig, hfr, hfr0⟩ := hpost
    have hbpn : (s.regs 4 - 16#64).toNat = (s.regs 4).toNat - 16 := by rw [BitVec.toNat_sub]; simp; omega
    have hbp0 : (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 16) 8 0).writeLE
        ((s.regs 4).toNat - 40) 8 4921126).readLE ((s.regs 4).toNat - 16) 8 = 0 := by
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
    have hfrn := hfr0 (by rw [hbpn]; exact hbp0)
    simp only [hbpn] at hfrn hbig
    dsimp only [setRegF] at hfrn hbig
    have hS4 : (s.regs 4 - 40#64).toNat = (s.regs 4).toNat - 40 := by rw [BitVec.toNat_sub]; simp; omega
    simp only [Nat.reduceEqDiff, ↓reduceIte, hS4] at hfrn
    have hretS : s'.mem.readLE (s.regs 4).toNat 8 = ret := by
      rw [hfrn.readLE (s.regs 4).toNat 8 (by
        simp only [outside_append, outside_cons, outside_nil, and_true]
        exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact h_ret
    janus64_run
    obtain ⟨P, hbo⟩ := hbig hbr
    have hbo0 := BigObj.of_bigOut hbo
    obtain ⟨ap, len, cap, hP, -⟩ := hbo
    have hv : val256 (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 16) 8 0).writeLE
        ((s.regs 4).toNat - 40) 8 4921126) z.toNat = val256 s.mem z.toNat := by
      have hzD := hzd
      unfold val256
      rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    have hf1 : MemFrame s.mem (((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 16) 8 0).writeLE
        ((s.regs 4).toNat - 40) 8 4921126) (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)]) :=
      (((MemFrame.refl _ _).writeLE_inRanges _ ⟨((s.regs 4).toNat - 4168, (s.regs 4).toNat), by simp, by omega, by omega⟩).writeLE_inRanges
        _ ⟨((s.regs 4).toNat - 4168, (s.regs 4).toNat), by simp, by omega, by omega⟩).writeLE_inRanges _
        ⟨((s.regs 4).toNat - 4168, (s.regs 4).toNat), by simp, by omega, by omega⟩
    refine ⟨fun h => h.elim, ⟨P, hP, ?_⟩, ?_⟩
    · rw [hv] at hbo0
      exact hbo0
    · refine hf1.trans hfrn (fun a n hh => ?_)
      simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
      exact ⟨hh, hh.1, by omega, by omega, by omega⟩

namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

/-- The stub runtime: generic code placed at `Extracted.program`'s own contract addresses. -/
def implAt : List Amd64.Segment := [newobjectSeg newA, wbSeg w1A, wbSeg w2A]

/-- The requests the witness runtime serves: `IntoBig`'s. -/
def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ (args = [bigType] ∨ args = [arrType])) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Amd64.Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

theorem model_new : NewobjectLiveContract64 (Extracted.program.ofImpl implAt) newA 4096 R := by janus64_live_newobject
theorem model_wb1 : WbLiveContract64 (Extracted.program.ofImpl implAt) w1A 4096 R 1 := by janus64_live_wb 1
theorem model_wb2 : WbLiveContract64 (Extracted.program.ofImpl implAt) w2A 4096 R 2 := by janus64_live_wb 2

theorem implOK : Amd64.ImplApart Extracted.program implAt := by
  unfold Amd64.ImplApart; constructor <;> decide

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
/-- the `uint256.Int` argument (32 readable bytes). -/
def zA : Nat := 0x300000

def dataByte (a : Nat) : Option Arm64.Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Arm64.Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else if a = sp0 + 1 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4168, 4176, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨zA, 32, false⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA

/-- `ToBig` of a non-nil `*uint256.Int`. -/
def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zV else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; match i, h with | 0, _ => rfl, rfl⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

theorem dataByte_none (a : Nat) (ha : 0x500000 ≤ a) : dataByte a = none := by
  unfold dataByte
  have : Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have h2 : d.base + d.bytes.length < 0x500000 := by
      have : ∀ d' ∈ Extracted.data, d'.base + d'.bytes.length < 0x500000 := by decide
      exact this d hd
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right; omega
  rw [this]

theorem bytes0_bump : mem0.readLE BUMP 8 = HEAP := by decide

theorem inv0 : R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 14).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega), if_neg (by simp only [sp0, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : StackGuardOK s0 4168 ∧ StackWritable s0 4168 8 ∧ (s0.regs 4).toNat % 8 = 0 ∧
    Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4168) 4176 R.rt ∧
    Apart ((s0.regs 14).toNat + 16) 8 ((s0.regs 4).toNat - 4168) 4168 ∧
    Outside ((s0.regs 14).toNat + 16) 8 R.rt ∧
    s0.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv 0x400 [] (s0.regs 14).toNat (view R.rt [] s0.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ 0x400 ∧
    (zV.toNat ≠ 0 → Buffer s0 zV 32 false ∧ Outside zV.toNat 32 R.rt ∧
      Janus.Spec.Disjoint zV.toNat 32 ((s0.regs 4).toNat - 4168) 4168) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide, dataLoaded, ?_, ?_, ?_,
    by decide, ?_, ?_, ?_, ?_, ?_, ?_, inv0, by decide, fun _ => ⟨⟨by decide, by decide⟩, ?_, ?_⟩⟩
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · simp only [Apart]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inr rfl⟩
  · rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rw [rt_eq]; simp only [outside_cons, outside_nil, and_true]; decide
  · unfold Janus.Spec.Disjoint; decide

open Fv256.CallSites

/-- The call states of the runtime stubs (U-WITNESS-CALLSITE): `s0`'s memory at the stub's entry, `RSP` at the call frame
(`s0`'s `RSP` less 32); `RAX` is the type descriptor for `runtime.newobject`. -/
def csNew : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 newA, regs := fun i => if i = 0 then BitVec.ofNat 64 bigType else if i = 4 then s0.regs 4 - 32#64 else s0.regs i }
def csW1 : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 w1A, regs := fun i => if i = 4 then s0.regs 4 - 32#64 else s0.regs i }
def csW2 : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 w2A, regs := fun i => if i = 4 then s0.regs 4 - 32#64 else s0.regs i }

theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr_new]; rfl
theorem csW1_rip : csW1.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") := by rw [addr_w1]; rfl
theorem csW2_rip : csW2.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") := by rw [addr_w2]; rfl

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, ?_⟩, ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · simp only [calleeStack64, outside_cons, outside_nil]; decide
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  · rw [rt_eq]; intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 :=
  ⟨by decide, by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 :=
  ⟨by decide, by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, liveSep_nil _,
    liveSep_one (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of `ToBig` on a
non-nil receiver satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (b : Nat) (z : BitVec 64) (ret : Nat) (s : State),
    Amd64.ImplApart Extracted.program impl ∧
    NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧
      WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ (L : List (Nat × Nat)) (b : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧
      WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 4168 ∧ StackWritable s 4168 8 ∧ (s.regs 4).toNat % 8 = 0 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4168) 4176 R.rt ∧
        Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4168) 4168 ∧
        Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
        blockSize 32 false + blockSize 32 true ≤ b ∧
        (z.toNat ≠ 0 → Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧
          Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4168) 4168)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (z.toNat = 0 → s'.regs 0 = 0) ∧
        (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4168, (s.regs 4).toNat)]) := by
  refine ⟨implAt, R, 0x400, zV, ret, s0, implOK, ?w1, ?w2, ?w3, ⟨[], 0x400, csNew, csNew_rip, csNew_pre⟩, ⟨[], 0x400, csW1, csW1_rip, csW1_pre⟩, ⟨[], 0x400, csW2, csW2_rip, csW2_pre⟩, hret, setup, pre,
    correctness implAt R 0x400 zV implOK ?w1 ?w2 ?w3 ret hret s0 setup pre⟩
  case w1 => exact by rw [addr_new]; exact model_new
  case w2 => exact by rw [addr_w1]; exact model_wb1
  case w3 => exact by rw [addr_w2]; exact model_wb2

end Witness

end Fv256.Amd64.ToBig
