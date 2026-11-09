import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.FM.IntoBigT
import Fv256.Proofs.Amd64.FormatBigDefs

/-!
# `(*uint256.Int).Format`, big path (iii), part A (amd64): `Format+0x1cc` to the return of `IntoBig`

`movq $0, 0x28(rsp)`; `rax := z` (the spill at `0x50(rsp)`); `rbx := &slot`; `call IntoBig`. `IntoBig` is a second function of the same
extraction (at `ibE`), proved about its own code and used as a callee summary exactly as in `ToBig`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.EqHashModel Janus.Contracts.ICall

namespace Fv256.Amd64.FormatBig

open Fv256.Amd64.IntoBig Fv256.FormatFast

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

/-- `Pre` of `IntoBig` with the nested facts about `*bp` dropped (the call site has `*bp = 0`). -/
def PreC (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Pib.DataLoaded s.mem ∧
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

set_option maxRecDepth 100000 in
theorem retAddr_filter : ∀ seg ∈ (Extracted.program.onlySegments [nmIB]).segments,
    Extracted.entry + 0x1e5 < seg.base ∨ seg.base + seg.bytes.length ≤ Extracted.entry + 0x1e5 := by decide

set_option maxRecDepth 100000 in
theorem retAddr_stub : ∀ st ∈ (Extracted.program.onlySegments [nmIB]).stubs, st.addr ≠ Extracted.entry + 0x1e5 := by decide

set_option maxRecDepth 100000 in
theorem retAddr_seg : ∃ a ∈ Extracted.program.segments, a.base ≤ Extracted.entry + 0x1e5 ∧
    Extracted.entry + 0x1e5 < a.base + a.bytes.length := by decide

theorem retAddr_call (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) : RetAddr (P0 impl) (Extracted.entry + 0x1e5) := by
  refine ⟨by decide, ?_, fun st hst => retAddr_stub st hst⟩
  intro seg hseg
  rcases List.mem_append.1 hseg with h | h
  · exact retAddr_filter seg h
  · obtain ⟨a, ha, h3, h4⟩ := retAddr_seg
    have hap := (List.pairwise_append.1 hI.1).2.2 a ha seg h
    unfold Amd64.Segment.Apart at hap
    omega

/-- the state after `IntoBig` returned: the frame registers kept, the memory changed only in the runtime's ranges, the callee window and the
slot; the slot holds a `big.Int` whose value is `z`'s, with both blocks in the runtime's ranges -/
def MidA (R2 : RtInv) (S S1 : State) (zv : Nat) : Prop :=
  S1.regs 4 = S.regs 4 ∧ S1.regs 5 = S.regs 5 ∧ S1.regs 14 = S.regs 14 ∧ S1.xmm 15 = S.xmm 15 ∧
  MemFrame S.mem S1.mem (R2.rt ++ [((S.regs 4).toNat - 8 - 4128, (S.regs 4).toNat + 16),
    ((S.regs 4).toNat + 0x28, (S.regs 4).toNat + 0x30)]) ∧
  ∃ P, S1.mem.readLE ((S.regs 4).toNat + 0x28) 8 = P ∧ Fv256.IntoBig.BigObj S1.mem P zv ∧ InRanges P 32 R2.rt ∧
    InRanges (S1.mem.readLE (P + 8) 8) 32 R2.rt

set_option maxRecDepth 20000 in
/-- the call state of `IntoBig(z, &slot)` (after `movq $0, 0x28(rsp)` and the push of the return address) satisfies the callee's precondition -/
theorem call_pre (R : RtInv) (b : Nat) (z : BitVec 64) (S sc : State) (v : Nat)
    (hsp : sc.regs 4 = S.regs 4 - 8#64) (hg : sc.regs 14 = S.regs 14)
    (hmem : sc.mem = (S.mem.writeLE ((S.regs 4).toNat + 0x28) 8 0).writeLE ((S.regs 4).toNat - 8) 8 v)
    (hg1 : (S.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true)
    (hg3 : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 4136 < (S.regs 4).toNat)
    (hgd : (S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ (S.regs 14).toNat + 16)
    (hal : (S.regs 4).toNat % 8 = 0) (hb' : 4136 ≤ (S.regs 4).toNat) (hrr : (S.regs 4).toNat + 0x78 ≤ 2 ^ 48)
    (hw : S.mem.accessible ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) true = true)
    (hd : Pib.DataLoaded S.mem)
    (hout : Outside ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) R.rt)
    (hgr : Outside ((S.regs 14).toNat + 16) 8 R.rt)
    (hflag : S.mem.accessible flagAddr 4 false = true) (hty1 : Outside bigType 16 R.rt) (hty2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b [] (S.regs 14).toNat (view R.rt [] S.mem)) (hbud : blockSize 32 false + blockSize 32 true ≤ b)
    (hza : S.mem.accessible z.toNat 32 false = true) (hz48 : z.toNat + 32 ≤ 2 ^ 48) (hzo : Outside z.toNat 32 R.rt)
    (hzd : z.toNat + 32 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ z.toNat) :
    PreC R b z (S.regs 4 + 40#64) sc ∧ Apart (S.regs 4 + 40#64).toNat 8 ((sc.regs 14).toNat + 16) 8 ∧
      sc.mem.readLE (S.regs 4 + 40#64).toNat 8 = 0 := by
  have hbpn : (S.regs 4 + 40#64).toNat = (S.regs 4).toNat + 40 := by rw [BitVec.toNat_add]; simp; omega
  have hspn : (sc.regs 4).toNat = (S.regs 4).toNat - 8 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hwS : S.mem.accessible ((S.regs 4).toNat + 0x28) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono S.mem hw (by omega) (by omega)
  have hacc : ∀ a n w, sc.mem.accessible a n w = S.mem.accessible a n w := by
    intro a n w; rw [hmem]; simp
  have ho1 : Outside ((S.regs 4).toNat + 0x28) 8 R.rt := hout.of_sub (by omega) (by omega)
  have ho2 : Outside ((S.regs 4).toNat - 8) 8 R.rt := hout.of_sub (by omega) (by omega)
  have hrd : ∀ a n, (a + n ≤ (S.regs 4).toNat - 8 ∨ (S.regs 4).toNat ≤ a) → (a + n ≤ (S.regs 4).toNat + 0x28 ∨ (S.regs 4).toNat + 0x30 ≤ a) →
      sc.mem.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hview : view R.rt [] sc.mem = view R.rt [] S.mem := by
    rw [hmem, view_writeLE_out ho2, view_writeLE_out ho1]
  have hbp0 : sc.mem.readLE ((S.regs 4).toNat + 40) 8 = 0 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hg14 : (sc.regs 14) = S.regs 14 := hg
  have hwv : (S.mem.writeLE ((S.regs 4).toNat + 0x28) 8 0).accessible ((S.regs 4).toNat - 8) 8 true = true := by
    rw [Janus.Arm64.Memory.accessible_writeLE]
    exact Janus.Arm64.Memory.accessible_mono S.mem hw (by omega) (by omega)
  have hdS : Pib.DataLoaded sc.mem := by
    rw [hmem]
    exact Fv256.E.dataLoaded_writeLE (Fv256.E.dataLoaded_writeLE hd hwS 0) hwv v
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, hdS, ?_, ?_, ?_, ?_, hty1, hty2, hok1, hok2, hok3, hok4, ?_, hbud, ⟨?_, ?_⟩, ?_, ?_, fun _ => ⟨⟨?_, ?_⟩, hzo, ?_, ?_⟩⟩
    · simp only [regG, stackguard0Offset, hg14]; omega
    · simp only [regG, stackguard0Offset, hg14, hacc]; exact hg2
    · simp only [regG, stackguard0Offset, stackguard0, hg14, hspn]; rw [hrd _ _ (by omega) (by omega)]; omega
    · rw [hspn]; omega
    · simp only [regSP, hspn]; omega
    · simp only [regSP, hacc, hspn]
      exact Janus.Arm64.Memory.accessible_mono S.mem hw (by omega) (by omega)
    · rw [hspn]; omega
    · rw [hspn]; exact hout.of_sub (by omega) (by omega)
    · rw [hg14, hspn]; unfold Apart; omega
    · rw [hg14]; exact hgr
    · rw [hacc]; exact hflag
    · rw [hg14, hview]; exact hinv
    · rw [hbpn]; omega
    · rw [hacc, hbpn]; exact hwS
    · rw [hbpn]; exact ho1
    · unfold Janus.Spec.Disjoint; rw [hbpn, hspn]; omega
    · exact hz48
    · rw [hacc]; exact hza
    · unfold Janus.Spec.Disjoint; rw [hspn]; omega
    · unfold Janus.Spec.Disjoint; rw [hbpn]; omega
  · unfold Apart; rw [hbpn, hg14]; omega
  · rw [hbpn]; exact hbp0

set_option maxRecDepth 20000 in
/-- from the postcondition of the `IntoBig` summary at the call state `sc` to `MidA` -/
theorem mid_of_post (R2 : RtInv) (b : Nat) (z : BitVec 64) (S sc s' : State) (v zv : Nat) (hz : z.toNat ≠ 0)
    (hsp : sc.regs 4 = S.regs 4 - 8#64) (h5 : sc.regs 5 = S.regs 5) (hg : sc.regs 14 = S.regs 14) (hx : sc.xmm 15 = S.xmm 15)
    (hmem : sc.mem = (S.mem.writeLE ((S.regs 4).toNat + 0x28) 8 0).writeLE ((S.regs 4).toNat - 8) 8 v)
    (hb' : 4136 ≤ (S.regs 4).toNat) (hwn : (S.regs 4).toNat + 0x78 ≤ 2 ^ 48) (hzv : sc.mem.readLE z.toNat 32 = zv)
    (hpost : (s'.regs 4 = sc.regs 4 + 8 ∧ s'.regs 5 = sc.regs 5 ∧ s'.regs 14 = sc.regs 14 ∧ s'.xmm 15 = sc.xmm 15) ∧
      Post R2 z (S.regs 4 + 40#64) sc s') :
    MidA R2 S s' zv := by
  obtain ⟨⟨h4', h5', h14', hx'⟩, -, hbig, -, hfr0, hin⟩ := hpost
  have hbpn : (S.regs 4 + 40#64).toNat = (S.regs 4).toNat + 40 := by rw [BitVec.toNat_add]; simp; omega
  have hspn : (sc.regs 4).toNat = (S.regs 4).toNat - 8 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  have hbp0' : sc.mem.readLE ((S.regs 4).toNat + 40) 8 = 0 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self]
  have hbp0 : sc.mem.readLE (S.regs 4 + 40#64).toNat 8 = 0 := by rw [hbpn]; exact hbp0'
  have hfrS : MemFrame S.mem sc.mem (R2.rt ++ [((S.regs 4).toNat - 8 - 4128, (S.regs 4).toNat + 16), ((S.regs 4).toNat + 0x28, (S.regs 4).toNat + 0x30)]) := by
    rw [hmem]
    exact ((MemFrame.refl S.mem _).writeLE_inRanges _ ⟨((S.regs 4).toNat + 0x28, (S.regs 4).toNat + 0x30), by simp, by omega, by omega⟩).writeLE_inRanges _
      ⟨((S.regs 4).toNat - 8 - 4128, (S.regs 4).toNat + 16), by simp, by omega, by omega⟩
  have hfr1 := hfr0 hbp0
  rw [hbpn, hspn] at hfr1
  obtain ⟨P, hbo⟩ := hbig hz
  rw [hbpn] at hbo
  obtain ⟨hinP, hinA⟩ := hin hz hbp0
  rw [hbpn] at hinP hinA
  have hbo1 := hbo
  obtain ⟨ap, len, cap, hbp, -⟩ := hbo1
  rw [hbp] at hinP hinA
  refine ⟨by rw [h4', hsp]; exact BitVec.sub_add_cancel _ _, by rw [h5', h5], by rw [h14', hg], by rw [hx', hx], ?_, P, by rw [hbpn] at *; exact hbp, ?_, hinP, hinA⟩
  · refine hfrS.trans hfr1 (fun a n h => ?_)
    simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨⟨h1, h2, h3⟩, h1, by omega, by omega, by omega⟩
  · have := Fv256.IntoBig.BigObj.of_bigOut hbo
    have hv : val256 sc.mem z.toNat = zv := hzv
    rw [hv] at this
    exact this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- the part of `big_A` after the setup: the `IntoBig` call from the call state `sc`, and the continuation -/
theorem after_setup (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) (R2 : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (z : BitVec 64) (zv : Nat) (S sc : State) (hz : z.toNat ≠ 0)
    (hsp : sc.regs 4 = S.regs 4 - 8#64) (h0 : sc.regs 0 = z) (h3 : sc.regs 3 = S.regs 4 + 40#64) (h5 : sc.regs 5 = S.regs 5)
    (h14 : sc.regs 14 = S.regs 14) (hx : sc.xmm 15 = S.xmm 15) (hdfS : sc.df = false) (hrip : sc.rip = BitVec.ofNat 64 Fv256.Amd64.IntoBig.ibE)
    (hmem : sc.mem = (S.mem.writeLE ((S.regs 4).toNat + 0x28) 8 0).writeLE ((S.regs 4).toNat - 8) 8 4923813)
    (hhx : S.xmm 15 = 0)
    (hg1S : (S.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2S : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true)
    (hgmS : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 4136 < (S.regs 4).toNat)
    (hgdS : (S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ (S.regs 14).toNat + 16)
    (hal : (S.regs 4).toNat % 8 = 0) (hb' : 4136 ≤ (S.regs 4).toNat) (hwn : (S.regs 4).toNat + 0x78 ≤ 2 ^ 48)
    (hw4568 : S.mem.accessible ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) true = true)
    (hdP : Pib.DataLoaded S.mem) (hR4568 : Outside ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) R2.rt)
    (hgRS : Outside ((S.regs 14).toNat + 16) 8 R2.rt)
    (hflagS : S.mem.accessible flagAddr 4 false = true) (hty1 : Outside bigType 16 R2.rt) (hty2 : Outside arrType 16 R2.rt)
    (hok1 : R2.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R2.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R2.inv b0 [] (S.regs 14).toNat (view R2.rt [] S.mem)) (hbud : blockSize 32 false + blockSize 32 true ≤ b0)
    (hzaS' : S.mem.accessible z.toNat 32 false = true) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hzoS : Outside z.toNat 32 R2.rt)
    (hzdS : z.toNat + 32 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ z.toNat)
    (hzvS : S.mem.readLE z.toNat 32 = zv) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1e5)) sc
      (fun S1 => MidA R2 S S1 zv) := by
  have hcn := codeIn_ofImpl_restrict_of_apart64 hI [nmIB]
  have hnew' := NewobjectLiveContract64.of_codeIn hcn hnew
  have hwb1' := WbLiveContract64.of_codeIn hcn hwb1
  have hwb2' := WbLiveContract64.of_codeIn hcn hwb2
  have SS := Ensures.toSummaryIn
    (Fv256.Amd64.IntoBig.correctness impl R2 b0 z (S.regs 4 + 40#64) hnew' hwb1' hwb2')
    (hx_IB impl hI) (by show 2 ≤ 9; decide) (codeIn_restrict_of_apart64 hI [nmIB])
  have SS' := Summary.mono SS
    (pre' := fun sc => RetAddr (P0 impl) (sc.mem.readLE (sc.regs regSP).toNat 8) ∧ sc.xmm xmmZero = 0 ∧
      ArgsFrom64 sc 0 [z, S.regs 4 + 40#64] ∧ sc.df = false ∧
      (PreC R2 b0 z (S.regs 4 + 40#64) sc ∧ Apart (S.regs 4 + 40#64).toNat 8 ((sc.regs 14).toNat + 16) 8 ∧
        sc.mem.readLE (S.regs 4 + 40#64).toNat 8 = 0))
    (fun sc ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, pre_mono h5 h6 h7⟩) (fun s s' _ h => h)
  have hspn : (sc.regs 4).toNat = (S.regs 4).toNat - 8 := by rw [hsp, BitVec.toNat_sub]; simp; omega
  refine ReachesRet.call SS' hrip ⟨?_, ?_, ?_, hdfS, call_pre R2 b0 z S sc 4923813 hsp h14 hmem hg1S hg2S hgmS hgdS hal hb' hwn hw4568 hdP hR4568 hgRS
    hflagS hty1 hty2 hok1 hok2 hok3 hok4 hinv hbud hzaS' hzb hzoS hzdS⟩ ?_
  · rw [show (sc.regs regSP) = sc.regs 4 from rfl, hspn, hmem, Janus.Arm64.Memory.readLE_writeLE_self]
    have : 4923813 % 256 ^ 8 = Extracted.entry + 0x1e5 := by decide
    rw [this]; exact retAddr_call impl hI
  · rw [show xmmZero = 15 from rfl]; rw [hx]; exact hhx
  · simp only [ArgsFrom64, argReg, intArgRegs]
    exact ⟨h0, h3, trivial⟩
  · intro s' hpc' hpost
    have hzv1 : sc.mem.readLE z.toNat 32 = zv := by
      rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
      exact hzvS
    refine ReachesRet.done ?_ (mid_of_post R2 b0 z S sc s' 4923813 zv hz hsp h5 h14 hx hmem hb' hwn hzv1 hpost)
    rw [hpc']
    simp only [retAddrOf, show (sc.regs regSP) = sc.regs 4 from rfl, hspn, hmem, Janus.Arm64.Memory.readLE_writeLE_self]
    have : 4923813 % 256 ^ 8 = Extracted.entry + 0x1e5 := by decide
    rw [this]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem big_A (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) (R2 : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hz : z.toNat ≠ 0)
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hrip : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x1cc))
    (hfi : FInv rt stack z tab data ch32 S0 S)
    (h4568 : 4568 ≤ stack)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt)
    (hdl : Extracted.program.DataLoaded S.mem)
    (hg1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (hgo : Outside ((S0.regs 14).toNat + 16) 8 rt)
    (hgd : (S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16)
    (hx0 : S0.xmm 15 = 0) (hdf0 : S0.df = false)
    (hbr : BigR2 R2 b0 z S0)
    (hinv : R2.inv b0 [] (S.regs 14).toNat (view R2.rt [] S.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1e5)) S
      (fun S1 => MidA R2 S S1 (S0.mem.readLE z.toNat 32)) := by
  have hft := finv_tab hpre hfi
  obtain ⟨-, -, -, -, -, hzvS, hzaS, hwaS⟩ := hft
  have hpre1 := hpre
  obtain ⟨h0', h3', h1', h5', hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  obtain ⟨hgm, hgR, hflag, hty1, hty2, hzR, hok1, hok2, hok3, hok4, hbud⟩ := hbr
  have hfi' := hfi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hfi
  have e4 : (S0.regs 4).toNat = (S.regs 4).toNat := by rw [i4]
  have e14 : (S.regs 14) = S0.regs 14 := i14
  have hr8 : (S.regs 4).toNat - 8 - 4568 ≥ (S.regs 4).toNat - 8 - stack := by omega
  rw [e4] at hwb hwn hal hwaS hwR hgd hgm hzd
  have hgmS : S.mem.readLE ((S.regs 14).toNat + 16) 8 + 4136 < (S.regs 4).toNat := by
    rw [e14, ifr.readLE _ _ (out_fl hgo (by omega) (by omega))]; omega
  have hgdS : (S.regs 14).toNat + 24 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ (S.regs 14).toNat + 16 := by
    rw [e14]; omega
  have hg2S : S.mem.accessible ((S.regs 14).toNat + 16) 8 false = true := by rw [ifr.accessible, e14]; exact hg2
  have hz50 : S.mem.readLE ((S.regs 4).toNat + 0x50) 8 = z.toNat := by rw [← e4]; exact i50
  have hwbS : S.mem.accessible ((S.regs 4).toNat + 0x28) 8 true = true :=
    Janus.Arm64.Memory.accessible_mono S.mem hwaS (by omega) (by omega)
  have hw4568 : S.mem.accessible ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) true = true :=
    Janus.Arm64.Memory.accessible_mono S.mem hwaS (by omega) (by omega)
  have hR4568 : Outside ((S.regs 4).toNat - 8 - 4568) (4568 + 0x80) R2.rt := hwR.of_sub (by omega) (by omega)
  have hzoS : Outside z.toNat 32 R2.rt := hzR
  have hzdS : z.toNat + 32 ≤ (S.regs 4).toNat - 8 - 4568 ∨ (S.regs 4).toNat + 0x78 ≤ z.toNat := by omega
  have hzaS' : S.mem.accessible z.toNat 32 false = true := hzaS
  have hhx : S.xmm 15 = 0 := by rw [ix]; exact hx0
  have hhdf : S.df = false := by rw [idf]; exact hdf0
  have hg1S : (S.regs 14).toNat + 24 ≤ 2 ^ 48 := by rw [e14]; exact hg1
  have hgRS : Outside ((S.regs 14).toNat + 16) 8 R2.rt := by rw [e14]; exact hgR
  have hflagS : S.mem.accessible flagAddr 4 false = true := by rw [ifr.accessible]; exact hflag
  have hdP : Pib.DataLoaded S.mem := Pib_dataLoaded hdl
  have hr8' : True := trivial
  have hg1S : (S.regs 14).toNat + 24 ≤ 2 ^ 48 := by rw [e14]; exact hg1
  have hgRS : Outside ((S.regs 14).toNat + 16) 8 R2.rt := by rw [e14]; exact hgR
  have hflagS : S.mem.accessible flagAddr 4 false = true := by rw [ifr.accessible]; exact hflag
  have hdP : Pib.DataLoaded S.mem := Pib_dataLoaded hdl
  janus64_run [hz50] until [Fv256.Amd64.IntoBig.ibE]
  exact after_setup impl hI R2 b0 hnew hwb1 hwb2 z _ S _ hz (by simp [setRegF_apply, i4]) (by simp [setRegF_apply]) (by simp [setRegF_apply, i4])
    (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp) (by first | rfl | simp [hhdf]) (by rfl) (by simp [i4]) hhx hg1S hg2S hgmS hgdS hal (by omega) hwn
    hw4568 hdP hR4568 hgRS hflagS hty1 hty2 hok1 hok2 hok3 hok4 hinv hbud hzaS' hzb hzoS hzdS hzvS

end Fv256.Amd64.FormatBig
