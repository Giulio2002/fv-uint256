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

namespace Fv256.Arm64.ToBig

open Fv256.Arm64.IntoBig

/-- The runtime stand-in `impl` is placed outside the extracted code: disjoint segments, no stub and not the exit
address at any of its instructions. -/
def ImplOK (impl : List Segment) : Prop :=
  (Extracted.program.segments ++ impl).Pairwise Segment.Apart ∧
    ∀ seg ∈ impl, ∀ i < seg.words.length,
      Extracted.program.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ Extracted.program.exitAddr

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

theorem apart_of {impl : List Segment} (hI : ImplOK impl) {a b : Segment} (ha : a ∈ Extracted.program.segments)
    (hb : b ∈ impl) : Segment.Apart a b := by
  have := List.pairwise_append.1 hI.1
  exact this.2.2 a ha b hb

/-- the instructions of `impl` are not fetched from the extraction's own segments -/
theorem impl_fetch_none {impl : List Segment} (hI : ImplOK impl) {seg : Segment} (hs : seg ∈ impl) {i : Nat}
    (hi : i < seg.words.length) (S : List Segment) (hS : ∀ x ∈ S, x ∈ Extracted.program.segments) :
    Program.fetchIn S (seg.base + 4 * i) = none := by
  apply fetchIn_none_of
  intro x hx j hj
  have hap := apart_of hI (hS x hx) hs
  unfold Segment.Apart at hap
  omega

theorem hc_IB (impl : List Segment) (hI : ImplOK impl) : CodeIn (P0 impl) (Extracted.program.link impl) := by
  apply codeIn_restrict Extracted.program [nmIB] impl hI.1
  intro seg hs i hi
  rcases List.mem_append.1 hs with h | h
  · exact ⟨by revert seg i; sorry, by revert seg i; sorry⟩
  · exact hI.2 seg h i hi

theorem hx_IB (impl : List Segment) (hI : ImplOK impl) : (P0 impl).fetch (P0 impl).exitAddr = none := by
  sorry

theorem hside (impl : List Segment) (hI : ImplOK impl) :
    ∀ seg ∈ impl, ∀ i < seg.words.length,
      (Extracted.program.onlySegments [nmIB]).fetch (seg.base + 4 * i) = none ∧
      Extracted.program.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ Extracted.program.exitAddr := by
  intro seg hs i hi
  refine ⟨impl_fetch_none hI hs hi _ (fun x hx => (List.mem_filter.1 hx).1), hI.2 seg hs i hi⟩

set_option maxRecDepth 20000 in
theorem correctness (impl : List Segment) (R : RtInv) (b : Nat) (z : BitVec 64)
    (hI : ImplOK impl)
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
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4192, s.sp.toNat), (0, 32)])) := by
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
  all_goals ((try clear hnew hwb1 hwb2 hnew' hwb1' hwb2' hcn S hI hok1 hok2 hok3 hok4 hty1 hty2 hout hga hgr hflag hinv hbud); trace_state; fail "probe")

end Fv256.Arm64.ToBig
