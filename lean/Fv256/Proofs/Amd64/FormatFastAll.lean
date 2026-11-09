import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Amd64.FormatFastPre
import Fv256.Proofs.Amd64.FormatFastDecPath
import Fv256.Proofs.Amd64.FormatFastHexPath

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast Fv256.E Fv256.Amd64.Dec

namespace Fv256.Amd64.FormatFast

/-- **(ii) the fast path, amd64.**  From the state `S0` just after the `z ≠ 0` split (`Format+0x45`): one run reaches either the
caller (`RIP` = the return address, with exactly one `Write` made, whose argument bytes are `fastBytes v ch` -- the call-site property
`FastWP data (fastBytes v ch)` of `hWr` -- after all four queries answered plain and `ch ∈ {d,v,s,x}`), or `Format+0x1cc` (the big path),
with the answers (`NotPlain`) that sent it there. -/
theorem fast_amd64 (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (RW RP RF RWr : Res) (z tab data : BitVec 64) (hI : ImplApart Extracted.program impl)
    (hW : ICallContract64 (Extracted.program.link impl) fW 1 stack 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2))
    (hP : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2))
    (hF : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 : State)
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes (S0.mem.readLE z.toNat 32) ((S0.regs 7).toNat % 2 ^ 32))))
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hcH : RtContract64 (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1)
    (hpc : S0.rip = BitVec.ofNat 64 (Extracted.entry + 0x45))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt)
    (h4568 : 4568 ≤ stack)
    (hdl : Extracted.program.DataLoaded S0.mem) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (ht1 : Outside 5163273 256 rt) (ht2 : Outside 5176582 256 rt) (ht3 : Outside 5142664 256 rt)
    (hg1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (hg3 : S0.mem.readLE ((S0.regs 14).toNat + 16) 8 + 0x378 < (S0.regs 4).toNat - 8)
    (hgo : Outside ((S0.regs 14).toNat + 16) 8 rt)
    (hgd : (S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16)
    (hx0 : S0.xmm 15 = 0) (hdf0 : S0.df = false)
    (hH1 : ∀ M, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → 2 ^ 64 ≤ S0.mem.readLE z.toNat 32 →
      H [0, (S0.regs 4).toNat - 8 - 0x178 + 86 + (98 - decLen (S0.mem.readLE z.toNat 32)), decLen (S0.mem.readLE z.toNat 32)]
        (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 0x178 - 8) (rtView rt M))
    (hH2 : ∀ M, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → 100 ≤ S0.mem.readLE z.toNat 32 →
      S0.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (S0.regs 4).toNat - 8 - 384 - 0x20 + (24 - decLen (S0.mem.readLE z.toNat 32)), decLen (S0.mem.readLE z.toNat 32)]
        (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 384 - 0x58) (rtView rt M))
    (hHst : ∀ M p l, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → StrOut M p l (decBytes (S0.mem.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l → H [0, p, l] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView rt M))
    (hHx : ∀ M, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → ∀ n, Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      H [0, (S0.regs 4).toNat - 8 - 112 + 38 + (64 - n), n + 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 112) (rtView rt M))
    (hHstx : ∀ M p l n, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      StrOut M p l (Fv256.C.hexStrBytes (S0.mem.readLE z.toNat 32) n) → InRanges p l rt →
      H [0, p + 2, l - 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView rt M))
    (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47) :
    RT (Extracted.program.link impl) S0
      [(S0.mem.readLE ((S0.regs 4).toNat + 72) 8, fun S' =>
          (S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
            S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
            MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
            (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) ∧
          (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
          ((S0.regs 7).toNat % 2 ^ 32 = 100 ∨ (S0.regs 7).toNat % 2 ^ 32 = 115 ∨ (S0.regs 7).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 7).toNat % 2 ^ 32 = 120)),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ((S0.regs 7).toNat % 2 ^ 32) S0 S' ∧ RPres R2 S0 S' ∧
          NotPlain RW RP RF data tab (S0.regs 7) fP fF ((S0.regs 7).toNat % 2 ^ 32))] := by
  have h0 := (pre_fast impl R2 rt stack fW fP fF fWr RW RP RF z tab data hW hP hF S0 hpc hpre hwR).regions
  refine RT.trans h0 ?_
  intro t ht S1 hr1 hq1
  simp only [List.map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · obtain ⟨⟨hi1, hpl, hv⟩, hreg1⟩ := hq1
    have h120 : (S0.regs 7).toNat % 2 ^ 32 ≠ 120 := by omega
    have hWr' : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
        (FastWP data (decBytes (S0.mem.readLE z.toNat 32))) := by
      simpa [Fv256.FormatSpec.fastBytes, h120] using hWr
    have kd := dec_path impl rt H stack fW fP fF fWr RWr z tab data _ hc S0 S1 hWr' hc2 hrt32 hr1 hpre hi1 h4568 hreg1 hdl hdrt
      ht1 ht2 hg1 hg2 hg3 hgo hgd hx0 hdf0 hH1 hH2 (by omega) hHst hret47
    have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S1
        (fun S' => (S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
            S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
            MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
            (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) ∧
          (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
          ((S0.regs 7).toNat % 2 ^ 32 = 100 ∨ (S0.regs 7).toNat % 2 ^ 32 = 115 ∨ (S0.regs 7).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 7).toNat % 2 ^ 32 = 120)) :=
      ReachesRet.mono kd (fun S' h => ⟨h, hpl, by omega⟩)
    refine RT.widen (RT.of_reachesRet k) ?_
    intro t ht; simp only [List.mem_singleton] at ht; subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · obtain ⟨⟨hi1, hpl, hv⟩, hreg1⟩ := hq1
    have hWr' : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
        (FastWP data (Fv256.FormatSpec.hexBytes (S0.mem.readLE z.toNat 32))) := by
      simpa [Fv256.FormatSpec.fastBytes, hv] using hWr
    have kd := hex_path impl rt H stack fW fP fF fWr RWr z tab data _ hI hcH S0 S1 _ hWr' hc2 hrt32 (by omega)
      (fun n hd => (hexBytes_digits n _ hd).symm) hHstx hret47 hr1 hpre hi1 (by omega) hdl hdrt hreg1 ht3 hg1 hg2 (by omega)
      hgo hgd hx0 hdf0 hHx
    have k : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S1
        (fun S' => (S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
            S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
            MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
            (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) ∧
          (∃ j3, PlainHist RW RP RF data tab (S0.regs 7) j3 fP fF) ∧
          ((S0.regs 7).toNat % 2 ^ 32 = 100 ∨ (S0.regs 7).toNat % 2 ^ 32 = 115 ∨ (S0.regs 7).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 7).toNat % 2 ^ 32 = 120)) :=
      ReachesRet.mono kd (fun S' h => ⟨h, hpl, by omega⟩)
    refine RT.widen (RT.of_reachesRet k) ?_
    intro t ht; simp only [List.mem_singleton] at ht; subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · obtain ⟨⟨hi1, hk1, hnp⟩, hreg1⟩ := hq1
    exact RT.here _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) hr1 ⟨hi1, hk1, hnp⟩

end Fv256.Amd64.FormatFast
