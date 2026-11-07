import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatFastPre
import Fv256.Arm64.FormatFastDecPath
import Fv256.Arm64.FormatFastHexPath

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.E Fv256.Arm64.Dec

namespace Fv256.Arm64.FormatFast

/-- **(ii) the fast path, arm64.**  From the state `S0` just after the `z ≠ 0` split (`Format+0x44`): one run reaches either the
caller (`PC` = the return address, with exactly one `Write` made, whose argument bytes are `fastBytes v ch` -- the call-site property
`FastWP data (fastBytes v ch)` of `hWr` -- after all four queries answered plain and `ch ∈ {d,v,s,x}`), or `Format+0x204` (the big path),
with the answers (`NotPlain`) that sent it there. -/
theorem fast_arm64 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (RW RP RF RWr : Res) (z tab data : BitVec 64) (hI : ImplApart Extracted.program impl)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True))
    (S0 : State)
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes (val256 S0.mem z.toNat) ((S0.regs 3).toNat % 2 ^ 32))))
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hcH : RtContract (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1)
    (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (h4608 : 4608 ≤ stack)
    (hdl : Extracted.program.DataLoaded S0.mem) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (ht1 : Outside 989280 256 rt) (ht2 : Outside 1002589 256 rt) (ht3 : Outside 968614 256 rt)
    (hg : GuardOK S0 688) (hgo : Outside ((S0.regs 28).toNat + 16) 8 rt)
    (hgd : (S0.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S0.regs 28).toNat + 16)
    (hH1 : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → 2 ^ 64 ≤ val256 S0.mem z.toNat →
      H [0, S0.sp.toNat - 384 + 94 + (98 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384) (rtView rt M))
    (hH2 : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → 100 ≤ val256 S0.mem z.toNat →
      val256 S0.mem z.toNat < 2 ^ 64 →
      H [0, S0.sp.toNat - 384 - 32 + (24 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384 - 96) (rtView rt M))
    (hHst : ∀ M p l, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → StrOut M p l (decBytes (val256 S0.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l → H [0, p, l] (S0.regs 28).toNat S0.sp.toNat (rtView rt M))
    (hHx : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → ∀ n, Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      H [0, S0.sp.toNat - 112 + 38 + (64 - n), n + 2] (S0.regs 28).toNat (S0.sp.toNat - 112) (rtView rt M))
    (hHstx : ∀ M p l n, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      StrOut M p l (Fv256.C.hexStrBytes (val256 S0.mem z.toNat) n) → InRanges p l rt →
      H [0, p + 2, l - 2] (S0.regs 28).toNat S0.sp.toNat (rtView rt M))
    (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    RT (Extracted.program.link impl) S0
      [(S0.mem.readLE S0.sp.toNat 8, fun S' =>
          (S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
            S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
            MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
            (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          ((S0.regs 3).toNat % 2 ^ 32 = 100 ∨ (S0.regs 3).toNat % 2 ^ 32 = 115 ∨ (S0.regs 3).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 3).toNat % 2 ^ 32 = 120)),
       (Extracted.entry + 0x204, fun S' => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧
          NotPlain RW RP RF data fW fP fF (S0.regs 3) ((S0.regs 3).toNat % 2 ^ 32))] := by
  have h0 := (pre_fast impl rt stack fW fP fF fWr RW RP RF z tab data hW hP hF S0 hpc hpre).regions
  refine RT.trans h0 ?_
  intro t ht S1 hr1 hq1
  simp only [List.map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hi1, hpl, hv⟩, hreg1⟩ := hq1
    have h120 : (S0.regs 3).toNat % 2 ^ 32 ≠ 120 := by omega
    have hWr' : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
        (FastWP data (decBytes (val256 S0.mem z.toNat))) := by
      simpa [Fv256.FormatSpec.fastBytes, h120] using hWr
    have kd := dec_path impl rt H stack fW fP fF fWr RWr z tab data _ hc S0 S1 hWr' hc2 hrt32 hr1 hpre hi1 h4608 hreg1 hdl hdrt
      ht1 ht2 hg hgo hgd hH1 hH2 hHst hret
    have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S1
        (fun S' => (S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
            S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
            MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
            (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          ((S0.regs 3).toNat % 2 ^ 32 = 100 ∨ (S0.regs 3).toNat % 2 ^ 32 = 115 ∨ (S0.regs 3).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 3).toNat % 2 ^ 32 = 120)) :=
      rr_mono kd (fun S' h => ⟨h, hpl, by omega⟩)
    refine RT.widen (RT.of_reachesRet k) ?_
    intro t ht; simp only [List.mem_singleton] at ht; subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · obtain ⟨⟨hi1, hpl, hv⟩, hreg1⟩ := hq1
    have hWr' : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
        (FastWP data (Fv256.FormatSpec.hexBytes (val256 S0.mem z.toNat))) := by
      simpa [Fv256.FormatSpec.fastBytes, hv] using hWr
    have kd := hex_path impl rt H stack fW fP fF fWr RWr z tab data _ hI hcH S0 S1 _ hWr' hc2 hrt32 h4608
      (fun n hd => (hexBytes_digits n _ hd).symm) hHstx hret hr1 hpre hi1 hdl hdrt hreg1 ht3
      ⟨hg.1, hg.2.1, by have := hg.2.2; omega⟩ hgo hgd hHx
    have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S1
        (fun S' => (S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
            S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
            MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
            (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          ((S0.regs 3).toNat % 2 ^ 32 = 100 ∨ (S0.regs 3).toNat % 2 ^ 32 = 115 ∨ (S0.regs 3).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 3).toNat % 2 ^ 32 = 120)) :=
      rr_mono kd (fun S' h => ⟨h, hpl, by omega⟩)
    refine RT.widen (RT.of_reachesRet k) ?_
    intro t ht; simp only [List.mem_singleton] at ht; subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · obtain ⟨⟨hi1, hnp⟩, hreg1⟩ := hq1
    exact RT.here _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hr1 ⟨hi1, hnp⟩

end Fv256.Arm64.FormatFast
