import Fv256.Arm64.CallSites.Base
import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.TB.IntoBigT

/-!
# `(*uint256.Int).ToBig() *big.Int` (arm64)

```go
func (z *Int) ToBig() *big.Int {
	if z == nil { return nil }
	var b *big.Int
	z.IntoBig(&b)
	return b
}
```
`IntoBig` is a second function of the same extraction. It is proved about its own code
(`(Extracted.program.onlySegments [IntoBig]).link impl`, the modules `Fv256.Arm64.TB.IntoBig*` are the
`IntoBig` proofs re-targeted mechanically at this extraction by `scripts/gen-tb-intobig.sh`) and used here as a
callee summary (`Ensures.toSummaryIn`). The runtime contracts are hypotheses about the program with no user code
(`Extracted.program.ofImpl impl`), moved up to the callee's and to the whole program.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.ToBig

open Fv256.Arm64.IntoBig

/-- the callee's name -/
abbrev nmIB : String := "github.com/holiman/uint256.(*Int).IntoBig"
/-- the callee's own program (with the runtime stand-in linked) -/
abbrev P0 (impl : List Segment) : Program := (Extracted.program.onlySegments [nmIB]).link impl

theorem fetchIn_none_of (segs : List Segment) (pc : Nat)
    (h : ∀ seg ∈ segs, ∀ i < seg.words.length, pc ≠ seg.base + 4 * i) : Program.fetchIn segs pc = none := by
  cases hf : Program.fetchIn segs pc with
  | none => rfl
  | some w =>
    obtain ⟨seg, hm, i, hi, hpc⟩ := Program.fetchIn_index hf
    exact absurd hpc (h seg hm i hi)

theorem apart_of {impl : List Segment} (hI : ImplApart Extracted.program impl) {a b : Segment} (ha : a ∈ Extracted.program.segments)
    (hb : b ∈ impl) : Segment.Apart a b := by
  have := List.pairwise_append.1 hI.1
  exact this.2.2 a ha b hb

/-- the instructions of `impl` are not fetched from the extraction's own segments -/
theorem impl_fetch_none {impl : List Segment} (hI : ImplApart Extracted.program impl) {seg : Segment} (hs : seg ∈ impl) {i : Nat}
    (hi : i < seg.words.length) (S : List Segment) (hS : ∀ x ∈ S, x ∈ Extracted.program.segments) :
    Program.fetchIn S (seg.base + 4 * i) = none := by
  apply fetchIn_none_of
  intro x hx j hj
  have hap := apart_of hI (hS x hx) hs
  unfold Segment.Apart at hap
  omega

theorem hc_IB (impl : List Segment) (hI : ImplApart Extracted.program impl) : CodeIn (P0 impl) (Extracted.program.link impl) :=
  codeIn_restrict Extracted.program [nmIB] impl hI.1 hI.2

theorem hx_IB (impl : List Segment) (hI : ImplApart Extracted.program impl) : (P0 impl).fetch (P0 impl).exitAddr = none := by
  apply fetchIn_none_of
  intro seg hseg i hi
  have hm : seg ∈ Extracted.program.segments ++ impl := by
    rcases List.mem_append.1 hseg with h | h
    · exact List.mem_append_left _ (List.mem_filter.1 h).1
    · exact List.mem_append_right _ h
  exact fun h => (hI.2 seg hm i hi).2 h.symm

theorem retAddr_filter : ∀ seg ∈ (Extracted.program.onlySegments [nmIB]).segments,
    Extracted.entry + 0x28 < seg.base ∨ seg.base + 4 * seg.words.length ≤ Extracted.entry + 0x28 := by decide

theorem retAddr_stub : ∀ st ∈ Extracted.program.stubs, st.addr ≠ Extracted.entry + 0x28 := by decide

theorem retAddr_seg : ∃ a ∈ Extracted.program.segments, a.base ≤ Extracted.entry + 0x28 ∧
    Extracted.entry + 0x28 < a.base + 4 * a.words.length := by decide

/-- the return site of the call to `IntoBig` is an admissible return address of the callee's program -/
theorem retAddr_call (impl : List Segment) (hI : ImplApart Extracted.program impl) : RetAddr (P0 impl) (Extracted.entry + 0x28) := by
  have h1 : (Extracted.entry + 0x28) % 4 = 0 := by decide
  have h2 : Extracted.entry + 0x28 < 2 ^ 48 := by decide
  refine ⟨h1, h2, ?_, fun st hst => retAddr_stub st hst⟩
  intro seg hseg
  rcases List.mem_append.1 hseg with h | h
  · exact retAddr_filter seg h
  · obtain ⟨a, ha, h3, h4⟩ := retAddr_seg
    have hap := apart_of hI ha h
    unfold Segment.Apart at hap
    omega

theorem hside (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    ∀ seg ∈ impl, ∀ i < seg.words.length,
      (Extracted.program.onlySegments [nmIB]).fetch (seg.base + 4 * i) = none ∧
      Extracted.program.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ Extracted.program.exitAddr := by
  intro seg hs i hi
  refine ⟨impl_fetch_none hI hs hi _ (fun x hx => (List.mem_filter.1 hx).1), hI.2 seg (List.mem_append_right _ hs) i hi⟩

theorem dataLoaded_writeLE {p : Program} {m : Memory} (hd : p.DataLoaded m) {a n v : Nat}
    (hw : m.accessible a n true = true) : p.DataLoaded (m.writeLE a n v) := by
  intro d hdm
  obtain ⟨hreg, hb⟩ := hd d hdm
  refine ⟨by simpa using hreg, fun i hi => ?_⟩
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdm
  have hdis := disjoint_of_dataLoaded hd k hk hw
  rw [hkd] at hdis
  rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  exact hb i hi

/-- The call state of `IntoBig(z, &b)` satisfies the callee's precondition. -/
theorem call_pre (R : RtInv) (b : Nat) (z : BitVec 64) (s sc : State) (X Y : Nat)
    (hsp : sc.sp = s.sp - 48#64) (hg : sc.regs 28 = s.regs 28)
    (hmem : sc.mem = ((s.mem.writeLE (s.sp.toNat - 48) 8 X).writeLE (s.sp.toNat - 56) 8 Y).writeLE
      (s.sp.toNat - 16) 8 0)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4192 < s.sp.toNat)
    (hal : s.sp.toNat % 16 = 0) (hb' : 4192 ≤ s.sp.toNat) (ha : s.sp.toNat + 0 ≤ 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 4192) (4192 + 0) true = true)
    (hd : Extracted.program.DataLoaded s.mem) (hout : Outside (s.sp.toNat - 4192) 4192 R.rt)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4192) 4192)
    (hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hflag : s.mem.accessible flagAddr 4 false = true) (hty1 : Outside bigType 16 R.rt)
    (hty2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem))
    (hbud : blockSize 32 false + blockSize 32 true ≤ b)
    (hz : z.toNat ≠ 0 → Ptr s.mem z 32 false ∧ Outside z.toNat 32 R.rt ∧
      Disjoint z.toNat 32 (s.sp.toNat - 4192) 4192) :
    Pre R b z (s.sp - 16#64) sc ∧ PreX z (s.sp - 16#64) sc := by
  have hsp' : sc.sp.toNat = s.sp.toNat - 48 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hbp : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by rw [BitVec.toNat_sub]; simp; omega
  have e : s.sp.toNat - 48 - 4144 = s.sp.toNat - 4192 := by omega
  have hacc : ∀ a n w, sc.mem.accessible a n w = s.mem.accessible a n w := by
    intro a n w; rw [hmem]; simp
  have hrd : ∀ a n, (a + n ≤ s.sp.toNat - 56 ∨ (s.sp.toNat - 40 ≤ a ∧ a + n ≤ s.sp.toNat - 16) ∨
      s.sp.toNat - 8 ≤ a) → sc.mem.readLE a n = s.mem.readLE a n := by
    intro a n h
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hview : view R.rt [] sc.mem = view R.rt [] s.mem := by
    rw [hmem, view_writeLE_out (Outside.of_sub hout (by omega) (by omega)),
      view_writeLE_out (Outside.of_sub hout (by omega) (by omega)),
      view_writeLE_out (Outside.of_sub hout (by omega) (by omega))]
  have hOut : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat → Outside a n R.rt :=
    fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
  have hwin : ∀ a n, s.sp.toNat - 4192 ≤ a → a + n ≤ s.sp.toNat → s.mem.accessible a n true = true :=
    fun a n h1 h2 => Janus.Arm64.Memory.accessible_sub s.mem hw (Or.inr rfl) h1 (by omega)
  have hbp0 : sc.mem.readLE (s.sp.toNat - 16) 8 = 0 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_self]
  unfold Apart at hga
  refine ⟨?_, ?_⟩
  · unfold Pre
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hok1, hok2, hok3, hok4, ?_, hbud, ?_, ?_, ?_, ?_⟩
    · rw [hg]; exact hg1
    · rw [hacc, hg]; exact hg2
    · rw [hg, hrd _ _ (by omega), hsp']; omega
    · rw [hsp']; omega
    · rw [hsp']; omega
    · rw [hsp']; omega
    · rw [hacc, hsp', e]; exact hwin _ _ (by omega) (by omega)
    · rw [hmem]
      exact dataLoaded_writeLE (dataLoaded_writeLE (dataLoaded_writeLE hd (hwin _ _ (by omega) (by omega)))
        (by simpa using hwin _ _ (by omega) (by omega))) (by simpa using hwin _ _ (by omega) (by omega))
    · rw [hsp', e]; exact hOut _ _ (by omega) (by omega)
    · rw [hg, hsp', e]; unfold Apart; omega
    · rw [hg]; exact hgr
    · rw [hacc]; exact hflag
    · exact hty1
    · exact hty2
    · rw [hg, hview]; exact hinv
    · refine ⟨?_, ?_⟩
      · rw [hacc, hbp]; exact hwin _ _ (by omega) (by omega)
      · rw [hbp]; omega
    · rw [hbp]; exact hOut _ _ (by omega) (by omega)
    · unfold Disjoint; rw [hbp, hsp', e]; omega
    · intro hz0
      obtain ⟨hzP, hzO, hzD⟩ := hz hz0
      unfold Disjoint at hzD
      refine ⟨⟨by rw [hacc]; exact hzP.1, hzP.2⟩, hzO, ?_, ?_, fun h => absurd (by rw [hbp]; exact hbp0) h⟩
      · unfold Disjoint; rw [hsp', e]; omega
      · unfold Disjoint; rw [hbp]; omega
  · unfold PreX
    refine ⟨?_, fun _ h => absurd (by rw [hbp]; exact hbp0) h⟩
    unfold Apart; rw [hg, hbp]; omega

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (z : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 4192 ∧ StackOK s 4192 0 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4192) 4192 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4192) 4192 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
        blockSize 32 false + blockSize 32 true ≤ b ∧
        (z.toNat ≠ 0 → Ptr s.mem z 32 false ∧ Outside z.toNat 32 R.rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 4192) 4192))
      (fun s s' => (z.toNat = 0 → s'.regs 0 = 0) ∧
        (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb', ha, hw⟩, hd, hout, hga, hgr, hflag, hty1, hty2, hok1, hok2, hok3, hok4, hinv, hbud, hz⟩
  have hcn := codeIn_ofImpl Extracted.program (Extracted.program.onlySegments [nmIB]) impl ⟨rfl, rfl⟩ (hside impl hI)
  have hnew' := NewobjectLiveContract.of_codeIn hcn hnew
  have hwb1' := WbLiveContract.of_codeIn hcn hwb1
  have hwb2' := WbLiveContract.of_codeIn hcn hwb2
  have S := Ensures.toSummaryIn
    (Fv256.Arm64.IntoBig.correctness impl R b z (s.sp - 16#64) hnew' hwb1' hwb2') (hx_IB impl hI) (hc_IB impl hI)
  janus_intro hs
  janus_data hd [hw]
  janus_run until [Extracted.entry + 0x60]
  · refine ⟨fun h => h.elim, ?_⟩
    janus_frame
  · have Sw := Summary.withExit S hret
    refine Reaches.call Sw (by rfl) ⟨?hRet, ?hArgs, call_pre R b z s _ ret (s.regs 29).toNat rfl (by simp [setReg])
      rfl hg1 hg2 hg3 hal hb' ha hw hd hout hga hgr hflag hty1 hty2 hok1 hok2 hok3 hok4 hinv hbud hz⟩
      (fun s' hpc' hpost => ?hcont)
    case hRet =>
      have e : BitVec.toNat (743240#64) = Extracted.entry + 0x28 := by decide
      show RetAddr _ (BitVec.toNat (743240#64))
      rw [e]; exact retAddr_call impl hI
    case hArgs =>
      simp [ArgsFrom, setReg, h_x0]
    case hcont =>
      obtain ⟨⟨hsp1, hg1', hfp1, h18'⟩, hzpost, hbig, hfr, hfr0⟩ := hpost
      dsimp only at hpc' hsp1 hg1' hfp1 h18' hbig hfr hfr0
      have hbpn : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by rw [BitVec.toNat_sub]; simp; omega
      have hbp0 : (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
          (s.sp.toNat - 16) 8 0).readLE (s.sp.toNat - 16) 8 = 0 := by
        rw [Janus.Arm64.Memory.readLE_writeLE_self]
      have hfrn := hfr0 (by rw [hbpn]; exact hbp0)
      obtain ⟨P, hbo⟩ := hbig hbr
      have hbo0 := BigObj.of_bigOut hbo
      obtain ⟨ap, len, cap, hP, -⟩ := hbo
      rw [hbpn] at hP
      simp only [setReg, regLR] at hpc' hg1' hfp1 h18'
      simp at hpc' hg1' hfp1 h18'
      have hspn : (s.sp - 48#64).toNat = s.sp.toNat - 48 := by rw [BitVec.toNat_sub]; simp; omega
      simp only [hspn, hbpn] at hfrn
      have hret48 := hret.user
      have hX29 : s'.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat := by
        rw [hfrn.readLE (s.sp.toNat - 56) 8 (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by simpa using (s.regs 29).isLt)
      have hX30 : s'.mem.readLE (s.sp.toNat - 48) 8 = ret := by
        rw [hfrn.readLE (s.sp.toNat - 48) 8 (by
          simp only [outside_append, outside_cons, outside_nil, and_true]
          exact ⟨Outside.of_sub hout (by omega) (by omega), by omega, by omega, by omega⟩)]
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
        exact Nat.mod_eq_of_lt (by simp; omega)
      have haccS : s'.mem.accessible (s.sp.toNat - 4192) 4192 true = true := by
        rw [hfrn.accessible]; simpa using hw
      janus_run
      have hv : val256 (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8 (s.regs 29).toNat).writeLE
          (s.sp.toNat - 16) 8 0) z.toNat = val256 s.mem z.toNat := by
        have hzD := (hz hbr).2.2
        unfold Disjoint at hzD
        unfold val256
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      have hf1 : MemFrame s.mem (((s.mem.writeLE (s.sp.toNat - 48) 8 ret).writeLE (s.sp.toNat - 56) 8
          (s.regs 29).toNat).writeLE (s.sp.toNat - 16) 8 0) (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat)]) :=
        (((MemFrame.refl _ _).writeLE_inRanges _ ⟨(s.sp.toNat - 4192, s.sp.toNat), by simp, by omega, by omega⟩).writeLE_inRanges
          _ ⟨(s.sp.toNat - 4192, s.sp.toNat), by simp, by omega, by omega⟩).writeLE_inRanges _
          ⟨(s.sp.toNat - 4192, s.sp.toNat), by simp, by omega, by omega⟩
      refine ⟨fun h => h.elim, ⟨P, hP, ?_⟩, ?_⟩
      · rw [hv] at hbo0
        rw [Janus.Spec.val256_limbs] at hbo0
        simpa using hbo0
      · refine hf1.trans hfrn (fun a n hh => ?_)
        simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
        refine ⟨hh, hh.1, ?_, ?_, ?_⟩ <;> omega


namespace Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")

/-- the stub runtime: generic code placed at `Extracted.program`'s own contract addresses -/
def implAt : List Segment := [newobjectSeg newA, wbSeg w1A, wbSeg w2A]

def ok : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ (args = [bigType] ∨ args = [arrType])) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2])

def R : RtInv := toyR [] ok

def linked : Program := Extracted.program.link implAt

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

theorem model_new : NewobjectLiveContract (Extracted.program.ofImpl implAt) newA 4096 R := by janus_live_newobject
theorem model_wb1 : WbLiveContract (Extracted.program.ofImpl implAt) w1A 4096 R 1 := by janus_live_wb 1
theorem model_wb2 : WbLiveContract (Extracted.program.ofImpl implAt) w2A 4096 R 2 := by janus_live_wb 2

theorem implOK : ImplApart Extracted.program implAt := by
  unfold ImplApart; constructor <;> decide

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zA : Nat := 0x300000

def dataByte (a : Nat) : Option Byte :=
  match Extracted.data.find? (fun d => decide (d.base ≤ a) && decide (a < d.base + d.bytes.length)) with
  | some d => some (BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0))
  | none => none

def bytes0 (a : Nat) : Byte :=
  match dataByte a with
  | some v => v
  | none => if a = BUMP + 3 then 0x10 else 0

def mem0 : Memory :=
  ⟨bytes0, [⟨sp0 - 4192, 4192, true⟩, ⟨g0, 0x100, false⟩, ⟨flagAddr, 8, false⟩, ⟨BUMP, 0x200, true⟩,
    ⟨HEAP, HSIZE, true⟩, ⟨zA, 32, false⟩] ++ Extracted.data.map fun d => ⟨d.base, d.bytes.length, false⟩⟩

def zV : BitVec 64 := BitVec.ofNat 64 zA

/-- `ToBig` of a non-nil `*uint256.Int` -/
def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [zV] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
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

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) bytes0_bump (fun i hi hi' => ?_) (by decide) (by decide) (by decide)
  show bytes0 i = 0
  simp only [bytes0, dataByte_none i (by simp only [HEAP] at hi; omega)]
  rw [if_neg (by simp only [BUMP, HEAP] at *; omega)]

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl

theorem pre : GuardOK s0 4192 ∧ StackOK s0 4192 0 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4192) 4192 R.rt ∧ Apart ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 4192) 4192 ∧
    Outside ((s0.regs 28).toNat + 16) 8 R.rt ∧
    s0.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ 0x400 ∧
    (zV.toNat ≠ 0 → Ptr s0.mem zV 32 false ∧ Outside zV.toNat 32 R.rt ∧ Disjoint zV.toNat 32 (s0.sp.toNat - 4192) 4192) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_,
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
  · unfold Disjoint; decide

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/ToBig.lean
/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `PC` at the stub's entry and the argument registers of a request `ok` serves. -/
def csNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 bigType else s0.regs i }
def csNew : State := { csNew0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csW1 : State := { s0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { s0 with sp := BitVec.ofNat 64 (sp0 - 48), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), typeOK_of (by decide) (by decide), by decide⟩, ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact Or.inl ⟨rfl, Or.inl (by decide)⟩
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w1]; exact Or.inr (Or.inl ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w2]; exact Or.inr (Or.inr ⟨rfl, rfl⟩), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

/-- All hypotheses of `correctness` hold together: a runtime (`impl`, `R`), a budget and a call of `ToBig` on a
non-nil receiver satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (b : Nat) (z : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 4192 ∧ StackOK s 4192 0 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4192) 4192 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4192) 4192 ∧
        Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
        s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
        R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
        R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
        R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
        blockSize 32 false + blockSize 32 true ≤ b ∧
        (z.toNat ≠ 0 → Ptr s.mem z 32 false ∧ Outside z.toNat 32 R.rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 4192) 4192)) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (z.toNat = 0 → s'.regs 0 = 0) ∧
        (z.toNat ≠ 0 → ∃ P : Nat, (s'.regs 0).toNat = P ∧ BigObj s'.mem P (val256 s.mem z.toNat)) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat)]) := by
  refine ⟨implAt, R, 0x400, zV, ret, s0, implOK, ?w1, ?w2, ?w3, hret, setup, pre,
    ⟨csNew, rfl, csNew_pre⟩,
    ⟨csW1, rfl, csW1_pre⟩,
    ⟨csW2, rfl, csW2_pre⟩,
    correctness implAt R 0x400 zV implOK ?w1 ?w2 ?w3 ret hret s0 setup pre⟩
  case w1 => exact by rw [addr_new]; exact model_new
  case w2 => exact by rw [addr_w1]; exact model_wb1
  case w3 => exact by rw [addr_w2]; exact model_wb2
end Witness

end Fv256.Arm64.ToBig
