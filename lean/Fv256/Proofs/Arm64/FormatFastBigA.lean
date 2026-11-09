import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Arm64.FM.IntoBigT

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Fv256.FormatFastA64 Fv256.Arm64.IntoBig

namespace Fv256.Arm64.FormatFast

abbrev nmIB : String := "github.com/holiman/uint256.(*Int).IntoBig"
abbrev P0B (impl : List Segment) : Program := (Extracted.program.onlySegments [nmIB]).link impl

theorem fetchIn_none_of' (segs : List Segment) (pc : Nat)
    (h : ∀ seg ∈ segs, ∀ i < seg.words.length, pc ≠ seg.base + 4 * i) : Program.fetchIn segs pc = none := by
  cases hf : Program.fetchIn segs pc with
  | none => rfl
  | some w =>
    obtain ⟨seg, hm, i, hi, hpc⟩ := Program.fetchIn_index hf
    exact absurd hpc (h seg hm i hi)

theorem hc_IB (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    CodeIn (P0B impl) (Extracted.program.link impl) :=
  codeIn_restrict Extracted.program [nmIB] impl hI.1 hI.2

theorem hx_IB (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    (P0B impl).fetch (P0B impl).exitAddr = none := by
  apply fetchIn_none_of'
  intro seg hseg i hi
  have hm : seg ∈ Extracted.program.segments ++ impl := by
    rcases List.mem_append.1 hseg with h | h
    · exact List.mem_append_left _ (List.mem_filter.1 h).1
    · exact List.mem_append_right _ h
  exact fun h => (hI.2 seg hm i hi).2 h.symm

theorem apart_of {impl : List Segment} (hI : ImplApart Extracted.program impl) {a b : Segment} (ha : a ∈ Extracted.program.segments)
    (hb : b ∈ impl) : Segment.Apart a b := by
  have := List.pairwise_append.1 hI.1
  exact this.2.2 a ha b hb

/-- the instructions of `impl` are not fetched from the extraction's own segments -/
theorem impl_fetch_none {impl : List Segment} (hI : ImplApart Extracted.program impl) {seg : Segment} (hs : seg ∈ impl) {i : Nat}
    (hi : i < seg.words.length) (S : List Segment) (hS : ∀ x ∈ S, x ∈ Extracted.program.segments) :
    Program.fetchIn S (seg.base + 4 * i) = none := by
  apply fetchIn_none_of'
  intro x hx j hj
  have hap := apart_of hI (hS x hx) hs
  unfold Segment.Apart at hap
  omega

theorem hside (impl : List Segment) (hI : ImplApart Extracted.program impl) :
    ∀ seg ∈ impl, ∀ i < seg.words.length,
      (Extracted.program.onlySegments [nmIB]).fetch (seg.base + 4 * i) = none ∧
      Extracted.program.stubAt (seg.base + 4 * i) = none ∧ seg.base + 4 * i ≠ Extracted.program.exitAddr := by
  intro seg hs i hi
  refine ⟨impl_fetch_none hI hs hi _ (fun x hx => (List.mem_filter.1 hx).1), hI.2 seg (List.mem_append_right _ hs) i hi⟩


/-- `IntoBig(z, bp)` as a summary in the whole program -/
def ib_summary (impl : List Segment) (hI : ImplApart Extracted.program impl) (R : RtInv) (b : Nat) (z bp : BitVec 64)
    (hnew : NewobjectLiveContract (P0B impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (P0B impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (P0B impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :=
  Ensures.toSummaryIn (Fv256.Arm64.IntoBig.correctness impl R b z bp hnew hwb1 hwb2) (hx_IB impl hI) (hc_IB impl hI)


set_option maxRecDepth 100000 in
theorem retAddr_filter : ∀ seg ∈ (Extracted.program.onlySegments [nmIB]).segments,
    Extracted.entry + 0x214 < seg.base ∨ seg.base + 4 * seg.words.length ≤ Extracted.entry + 0x214 := by decide

set_option maxRecDepth 100000 in
theorem retAddr_stub : ∀ st ∈ Extracted.program.stubs, st.addr ≠ Extracted.entry + 0x214 := by decide

set_option maxRecDepth 100000 in
theorem retAddr_seg : ∃ a ∈ Extracted.program.segments, a.base ≤ Extracted.entry + 0x214 ∧
    Extracted.entry + 0x214 < a.base + 4 * a.words.length := by decide

theorem retAddr_call (impl : List Segment) (hI : ImplApart Extracted.program impl) : RetAddr (P0B impl) (Extracted.entry + 0x214) := by
  have h1 : (Extracted.entry + 0x214) % 4 = 0 := by decide
  have h2 : Extracted.entry + 0x214 < 2 ^ 48 := by decide
  refine ⟨h1, h2, ?_, fun st hst => retAddr_stub st hst⟩
  intro seg hseg
  rcases List.mem_append.1 hseg with h | h
  · exact retAddr_filter seg h
  · obtain ⟨a, ha, h3, h4⟩ := retAddr_seg
    have hap := apart_of hI ha h
    unfold Segment.Apart at hap
    omega

theorem dataLoaded_writeLE' {p : Program} {m : Memory} (hd : p.DataLoaded m) {a n v : Nat}
    (hw : m.accessible a n true = true) : p.DataLoaded (m.writeLE a n v) := by
  intro d hdm
  obtain ⟨hreg, hb⟩ := hd d hdm
  refine ⟨by simpa using hreg, fun i hi => ?_⟩
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdm
  have hdis := disjoint_of_dataLoaded hd k hk hw
  rw [hkd] at hdis
  rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  exact hb i hi

/-- The call state of `IntoBig(z, &slot)` (after `str xzr,[sp+48]`) satisfies the callee's precondition. -/
theorem call_pre (R : RtInv) (b : Nat) (z : BitVec 64) (S sc : State)
    (hsp : sc.sp = S.sp) (hg : sc.regs 28 = S.regs 28) (hmem : sc.mem = S.mem.writeLE (S.sp.toNat + 48) 8 0)
    (hg1 : (S.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : S.mem.accessible ((S.regs 28).toNat + 16) 8 false = true)
    (hg3 : S.mem.readLE ((S.regs 28).toNat + 16) 8 + 4144 < S.sp.toNat)
    (hal : S.sp.toNat % 16 = 0) (hb' : 4144 ≤ S.sp.toNat) (ha : S.sp.toNat + 24 ≤ 2 ^ 48)
    (hw : S.mem.accessible (S.sp.toNat - 4144) (4144 + 24) true = true)
    (hwb : S.mem.accessible (S.sp.toNat + 48) 8 true = true) (hbd : S.sp.toNat + 56 ≤ 2 ^ 48)
    (hd : Pib.DataLoaded S.mem) (hout : Outside (S.sp.toNat - 4144) 4168 R.rt)
    (hbpo : Outside (S.sp.toNat + 48) 8 R.rt)
    (hga : Apart ((S.regs 28).toNat + 16) 8 (S.sp.toNat - 4144) 4168)
    (hgr : Outside ((S.regs 28).toNat + 16) 8 R.rt)
    (hgbp : Apart (S.sp.toNat + 48) 8 ((S.regs 28).toNat + 16) 8)
    (hflag : S.mem.accessible flagAddr 4 false = true) (hty1 : Outside bigType 16 R.rt)
    (hty2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b [] (S.regs 28).toNat (view R.rt [] S.mem))
    (hbud : blockSize 32 false + blockSize 32 true ≤ b)
    (hzp : Ptr S.mem z 32 false) (hzo : Outside z.toNat 32 R.rt)
    (hzd : Disjoint z.toNat 32 (S.sp.toNat - 4144) 4168) (hzbp : Disjoint z.toNat 32 (S.sp.toNat + 48) 8) :
    Pre R b z (S.sp + 48#64) sc ∧ PreX z (S.sp + 48#64) sc := by
  have hbpn : (S.sp + 48#64).toNat = S.sp.toNat + 48 := by rw [BitVec.toNat_add]; simp; omega
  have hacc : ∀ a n w, sc.mem.accessible a n w = S.mem.accessible a n w := by
    intro a n w; rw [hmem]; simp
  have hrd : ∀ a n, (a + n ≤ S.sp.toNat + 48 ∨ S.sp.toNat + 56 ≤ a) → sc.mem.readLE a n = S.mem.readLE a n := by
    intro a n h
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hview : view R.rt [] sc.mem = view R.rt [] S.mem := by
    rw [hmem, view_writeLE_out hbpo]
  have hbp0 : sc.mem.readLE (S.sp.toNat + 48) 8 = 0 := by
    rw [hmem, Janus.Arm64.Memory.readLE_writeLE_self]
  unfold Apart at hga hgbp
  unfold Disjoint at hzd hzbp
  refine ⟨?_, ?_⟩
  · unfold Pre
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hok1, hok2, hok3, hok4, ?_, hbud, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hg]; exact hg1
    · rw [hacc, hg]; exact hg2
    · rw [hg, hrd _ _ (by omega), hsp]; exact hg3
    · rw [hsp]; exact hal
    · rw [hsp]; exact hb'
    · rw [hsp]; omega
    · rw [hacc, hsp]; exact hw
    · rw [hmem]; exact dataLoaded_writeLE' hd hwb
    · rw [hsp]; exact hout
    · rw [hg, hsp]; unfold Apart; exact hga
    · rw [hg]; exact hgr
    · rw [hacc]; exact hflag
    · exact hty1
    · exact hty2
    · rw [hg, hview]; exact hinv
    · rw [hacc, hbpn]; exact hwb
    · rw [hbpn]; omega
    · rw [hbpn]; exact hbpo
    · unfold Disjoint; rw [hbpn, hsp]; omega
    · intro hz0
      refine ⟨⟨by rw [hacc]; exact hzp.1, hzp.2⟩, hzo, ?_, ?_, fun h => absurd (by rw [hbpn]; exact hbp0) h⟩
      · unfold Disjoint; rw [hsp]; omega
      · unfold Disjoint; rw [hbpn]; omega
  · unfold PreX
    refine ⟨?_, fun _ h => absurd (by rw [hbpn]; exact hbp0) h⟩
    unfold Apart; rw [hg, hbpn]; omega

set_option janus.callRegions true in
set_option maxRecDepth 20000 in
/-- the big path, part A: `*slot = 0`, `IntoBig(z, &slot)` from `Format+0x204`, return at `Format+0x214` -/
theorem big_a (impl : List Segment) (hI : ImplApart Extracted.program impl) (R : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x204))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4608 : 4608 ≤ stack) (hz0 : z.toNat ≠ 0)
    (hdl : Extracted.program.DataLoaded S.mem) (hg : GuardOK S 4144)
    (hga : Apart ((S.regs 28).toNat + 16) 8 (S.sp.toNat - 4144) 4168) (hgr : Outside ((S.regs 28).toNat + 16) 8 R.rt)
    (hfl : S.mem.accessible flagAddr 4 false = true) (ht1 : Outside bigType 16 R.rt) (ht2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b0 [] (S.regs 28).toNat (view R.rt [] S.mem)) (hbud : blockSize 32 false + blockSize 32 true ≤ b0)
    (hRout : Outside (S0.sp.toNat - stack) (stack + 0x78) R.rt) (hzR : Outside z.toNat 32 R.rt)
    (hgbp : Apart (S0.sp.toNat + 48) 8 ((S.regs 28).toNat + 16) 8) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x214)) S
      (fun S1 => S1.sp = S.sp ∧ S1.regs 29 = S.regs 29 ∧ S1.regs 28 = S.regs 28 ∧ S1.regs 18 = S.regs 18 ∧
        (∃ P : Nat, BigOut S1.mem (S0.sp.toNat + 48) P (val256 S0.mem z.toNat)) ∧
        MemFrame S.mem S1.mem (R.rt ++ [(S0.sp.toNat - 4144, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 24),
          (S0.sp.toNat + 48, S0.sp.toNat + 56)])) := by
  have hcn := codeIn_ofImpl Extracted.program (Extracted.program.onlySegments [nmIB]) impl ⟨rfl, rfl⟩ (hside impl hI)
  have hnew' := NewobjectLiveContract.of_codeIn hcn hnew
  have hwb1' := WbLiveContract.of_codeIn hcn hwb1
  have hwb2' := WbLiveContract.of_codeIn hcn hwb2
  have hS := ib_summary impl hI R b0 z (S.sp + 48#64) hnew' hwb1' hwb2'
  have hi' := hi
  have hpre1 := hpre
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  obtain ⟨-, -, -, -, -, hzr, hza, hwaS⟩ := finv_tab hpre1 hi'
  have hspn : S.sp.toNat = S0.sp.toNat := by rw [i4]
  have hbpn : (S.sp + 48#64).toNat = S0.sp.toNat + 48 := by rw [BitVec.toNat_add]; simp; omega
  have hview : view R.rt [] (S.mem.writeLE (S0.sp.toNat + 48) 8 0) = view R.rt [] S.mem :=
    view_writeLE_out (Outside.of_sub hRout (by omega) (by omega))
  have hSb : S.sp.toNat + 24 ≤ 2 ^ 48 := by omega
  have hsp0 : S.sp = S0.sp := i4
  janus_run [i88, hsp0] until [Fv256.Arm64.IntoBig.ibEntry]
  have hbwr : S.mem.accessible (S.sp.toNat + 48) 8 true = true := by
    rw [hspn]
    exact Janus.Arm64.Memory.accessible_sub S.mem hwaS (Or.inr rfl) (by omega) (by omega)
  have hwin : S.mem.accessible (S.sp.toNat - 4144) (4144 + 24) true = true := by
    rw [hspn]
    exact Janus.Arm64.Memory.accessible_sub S.mem hwaS (Or.inr rfl) (by omega) (by omega)
  have hzv : val256 S.mem z.toNat = val256 S0.mem z.toNat := hzr
  have hzdS : z.toNat + 32 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ z.toNat := hzd
  refine ReachesRet.call hS (by rfl) ⟨?_, ?_, call_pre R b0 z S _ hsp0.symm (by simp [setReg_apply]) (by simp [hsp0]) hg.1 hg.2.1 hg.2.2
    (by rw [hspn]; exact hal) (by omega) hSb hwin hbwr (by omega) (Pib_dataLoaded hdl) (by rw [hspn]; exact hRout.of_sub (by omega) (by omega))
    (by rw [hspn]; exact hRout.of_sub (by omega) (by omega)) hga hgr (by rw [hspn]; exact hgbp) hfl ht1 ht2 hok1 hok2 hok3 hok4 hinv hbud
    ⟨hza, hzp.2⟩ hzR (by unfold Disjoint; rw [hspn]; omega) (by unfold Disjoint; rw [hspn]; omega)⟩ ?_
  · have e : BitVec.toNat (746052#64) = Extracted.entry + 0x214 := by decide
    show RetAddr _ (BitVec.toNat (746052#64))
    rw [e]; exact retAddr_call impl hI
  · simp [ArgsFrom, setReg_apply, hsp0]
  intro s' hpc' ⟨⟨hsp1, hg1', hfp1, h18'⟩, hz0p, hbig, hfr, hfr0⟩
  dsimp only at hpc' hsp1 hg1' hfp1 h18' hz0p hbig hfr hfr0
  have hbp0 : (S.mem.writeLE (S0.sp.toNat + 48) 8 0).readLE (S0.sp.toNat + 48) 8 = 0 := by rw [Janus.Arm64.Memory.readLE_writeLE_self]
  have hbpn : (S.sp + 48#64).toNat = S0.sp.toNat + 48 := by rw [BitVec.toNat_add]; simp; omega
  rw [hbpn] at hfr0 hbig
  have hfrn := hfr0 hbp0
  rw [show (S0.sp).toNat = S0.sp.toNat from rfl] at hfrn
  obtain ⟨P, hbo⟩ := hbig hz0
  have hzv' : val256 (S.mem.writeLE (S0.sp.toNat + 48) 8 0) z.toNat = val256 S0.mem z.toNat := by
    rw [← hzv]; unfold val256
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  rw [hzv'] at hbo
  have hfrS : MemFrame S.mem (S.mem.writeLE (S0.sp.toNat + 48) 8 0) (R.rt ++ [(S0.sp.toNat - 4144, S0.sp.toNat - 8),
      (S0.sp.toNat + 8, S0.sp.toNat + 24), (S0.sp.toNat + 48, S0.sp.toNat + 56)]) :=
    MemFrame.of_writeLE S.mem _ (r := (S0.sp.toNat + 48, S0.sp.toNat + 56)) (by simp) (by omega) (by omega)
  simp only [setReg_apply, regLR] at hpc' hg1' hfp1 h18'
  simp at hpc' hg1' hfp1 h18'
  refine ReachesRet.done ?_ ⟨?_, ?_, ?_, ?_, ⟨P, hbo⟩, hfrS.trans hfrn fun a n h => ⟨h, h⟩⟩
  · rw [hpc']; simp [Extracted.entry]
  · rw [hsp1]; exact hsp0.symm
  · rw [hfp1]
  · rw [hg1']
  · rw [h18']

end Fv256.Arm64.FormatFast
