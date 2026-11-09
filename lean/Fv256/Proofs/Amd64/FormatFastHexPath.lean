import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Common.SegCompose
import Fv256.Proofs.Amd64.FormatFastHex
import Fv256.Proofs.Amd64.FormatFastStbX
import Fv256.Proofs.Amd64.FormatFastWr

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- the `x` path from `Format+0x176` to the return: `Hex(z)`, `[2:]`, `stringtoslicebyte`, one `Write` of the digits (`bsH`), epilogue -/
theorem hex_path (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (RWr : Res) (z tab data : BitVec 64) (ch32 : Nat) (hI : ImplApart Extracted.program impl)
    (hc : RtContract64 (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State) (bsH : List Nat)
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr (FastWP data bsH))
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1) (h4096 : 4096 ≤ stack)
    (hbsH : ∀ n, Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      (List.range n).map (fun k => Fv256.C.hexChar (S0.mem.readLE z.toNat 32 / 16 ^ (n - 1 - k) % 16)) = bsH)
    (hHst : ∀ M p l n, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      Janus.Contracts.StrOut M p l (Fv256.C.hexStrBytes (S0.mem.readLE z.toNat 32) n) → InRanges p l rt →
      H [0, p + 2, l - 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView rt M))
    (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x176))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4208 : 4208 ≤ stack) (hdl : Extracted.program.DataLoaded S0.mem)
    (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) (hreg : S.mem.regions = S0.mem.regions)
    (ht1 : Outside 5142664 256 rt)
    (hg1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (hg3 : S0.mem.readLE ((S0.regs 14).toNat + 16) 8 < (S0.regs 4).toNat - 8)
    (hgo : Outside ((S0.regs 14).toNat + 16) 8 rt)
    (hgd : (S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16)
    (hx0 : S0.xmm 15 = 0) (hdf0 : S0.df = false)
    (hHx : ∀ M, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → ∀ n, Fv256.C.hexDigits (S0.mem.readLE z.toNat 32) n →
      H [0, (S0.regs 4).toNat - 8 - 112 + 38 + (64 - n), n + 2] (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 112) (rtView rt M)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
      (fun S' => S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
        S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
        MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
        (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) := by
  have hpre0 := hpre
  obtain ⟨-, -, -, -, -, hwb, -, hwa0, hout, -⟩ := hpre0
  refine Fv256.SegCompose.seg_trans (hex_call impl rt H stack fW fP fF fWr z tab data ch32 hI hc S0 S hpc hpre hi h4208 hdl hdrt hreg ht1 hg1 hg2 hg3 hgo hgd hx0 hdf0 hHx) ?_
  intro S1 hr1 hq1
  obtain ⟨hi1, ⟨n, hd, hso1⟩, hIn1, hreg1, hdl1⟩ := hq1
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hso1
  have hv256 : S0.mem.readLE z.toNat 32 < 2 ^ 256 := by simpa using Janus.Arm64.Memory.readLE_lt S0.mem z.toNat 32
  have hn64 := hexDigits_le64 _ _ hv256 hd
  have hlenH : (Fv256.C.hexStrBytes (S0.mem.readLE z.toNat 32) n).length = n + 2 := by simp [Fv256.C.hexStrBytes]
  have hbsE := hbsH n hd
  have hbsl : bsH.length = n := by rw [← hbsE]; simp
  have hdrop : (Fv256.C.hexStrBytes (S0.mem.readLE z.toNat 32) n).drop 2 = bsH := by rw [← hbsE]; simp [Fv256.C.hexStrBytes]
  have e : (S1.regs 3).toNat = n + 2 := by omega
  have hn1 : 1 ≤ n := hd.1
  have hbsS : Janus.Spec.strBytes S1.mem ((S1.regs 0).toNat + 2) ((S1.regs 3).toNat - 2) = bsH := by
    have hl4' := hl4
    rw [e] at hl4'
    rw [e, Nat.add_sub_cancel, strBytes_drop2, hl4', hdrop]
  obtain ⟨r, hr, h1, h2⟩ := hIn1
  have hdis1 := MemFrame.outside_mem hout hr
  have h0S1 : S1.regs 0 = BitVec.ofNat 64 (S1.regs 0).toNat := by simp
  have h3S1 : S1.regs 3 = BitVec.ofNat 64 (S1.regs 3).toNat := by simp
  refine Fv256.SegCompose.seg_trans (stb_hex impl rt H stack fW fP fF fWr z tab data ch32 bsH (S1.regs 0).toNat (S1.regs 3).toNat hc2 S0 S1 hr1
    hpre hi1 h4096 h0S1 h3S1 (by omega) (by omega) (by omega) hl2 hl3 hbsS (by omega) (by have := hrt32 r hr; omega)
    (hHst S1.mem _ _ n hi1.2.2.2.2.1 hd ⟨hl1, hl2, hl3, hl4⟩ ⟨r, hr, h1, h2⟩)) ?_
  intro S2 hr2 hq2
  obtain ⟨hi2, r0, r1, r2, e0, e3, e1, hr1l, hr2pos, hr264, hIn, hBH⟩ := hq2
  obtain ⟨hlc, hp48, hacc, hstr, -⟩ := hBH
  obtain ⟨r', hr', hrr1, hrr2⟩ := hIn
  have hdis2 := MemFrame.outside_mem hout hr'
  refine ReachesRet.mono (wrh_call impl rt stack fW fP fF fWr RWr z tab data ch32 bsH r0 r1 r2 hWr S0 S2 hr2 hpre hi2
    e0 e3 e1 (by omega) hstr (by omega) (fun h => Janus.Arm64.Memory.accessible_sub S2.mem (Janus.Arm64.Memory.accessible_read_of_write _ hacc) (Or.inl rfl) (by omega) (by omega)) hlc hr264 hret47 (by omega)) (fun S' h => ?_)
  obtain ⟨a1, a2, a3, a4, a5, j0, j3, j1, hR⟩ := h
  exact ⟨a1, a2, a3, a4, a5, r0, r1, r2, j0, j3, j1, hR⟩

end Fv256.Amd64.FormatFast
