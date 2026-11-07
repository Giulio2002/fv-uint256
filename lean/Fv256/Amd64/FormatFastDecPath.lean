import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
import Fv256.SegCompose
import Fv256.Amd64.FormatFastDec
import Fv256.Amd64.FormatFastDecStr
import Fv256.Amd64.FormatFastStb
import Fv256.Amd64.FormatFastWr

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast Fv256.E Fv256.Amd64.Dec

namespace Fv256.Amd64.FormatFast

/-- the `d`, `v`, `s` path from `Format+0x139` to the return: `Dec(z)`, `stringtoslicebyte`, one `Write` of `decBytes v`, epilogue -/
theorem dec_path (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat) (RWr : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State)
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr
      (FastWP data (decBytes (S0.mem.readLE z.toNat 32))))
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1)
    (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x139))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4568 : 4568 ≤ stack) (hreg : S.mem.regions = S0.mem.regions)
    (hdl : Extracted.program.DataLoaded S0.mem) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (ht1 : Outside 5163273 256 rt) (ht2 : Outside 5176582 256 rt)
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
    (h4096 : 4096 ≤ stack)
    (hHst : ∀ M p l, MemFrame S0.mem M (FL rt (S0.regs 4).toNat stack) → StrOut M p l (decBytes (S0.mem.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l → H [0, p, l] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView rt M))
    (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
      (fun S' => S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
        S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧
        MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
        (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) := by
  have hpre0 := hpre
  obtain ⟨-, -, -, -, -, hwb, -, hwa0, hout, -⟩ := hpre0
  refine Fv256.SegCompose.seg_trans (dec_call impl rt H stack fW fP fF fWr z tab data ch32 hc S0 S hpc hpre hi h4568 hreg hdl hdrt ht1 ht2 hg1 hg2 hg3 hgo hgd hx0 hdf0 hH1 hH2) ?_
  intro S1 hr1 hq1
  obtain ⟨hi1, hso1, hDA1, hreg1, hdl1⟩ := hq1
  obtain ⟨-, -, -, -, -, -, -, hwa1⟩ := finvD_tab hpre hi1
  obtain ⟨hdis1, h321⟩ := dec_str_out hdl1 hwa1 hout hrt32 hDA1
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hso1
  have hv256 : S0.mem.readLE z.toNat 32 < 2 ^ 256 := by simpa using Janus.Arm64.Memory.readLE_lt S0.mem z.toNat 32
  have hd78 : decLen (S0.mem.readLE z.toNat 32) ≤ 78 :=
    decLen_le_of_lt_pow _ 78 (by omega) (Nat.lt_of_lt_of_le hv256 (by decide))
  have hd1 := decLen_pos (S0.mem.readLE z.toNat 32)
  have hlenE : (decBytes (S0.mem.readLE z.toNat 32)).length = decLen (S0.mem.readLE z.toNat 32) := rfl
  have h0S1 : S1.regs 0 = BitVec.ofNat 64 (S1.regs 0).toNat := by simp
  have h3S1 : S1.regs 3 = BitVec.ofNat 64 (S1.regs 3).toNat := by simp
  refine Fv256.SegCompose.seg_trans (stb_dec impl rt H stack fW fP fF fWr z tab data ch32 (decBytes (S0.mem.readLE z.toNat 32))
    (S1.regs 0).toNat (S1.regs 3).toNat hc2 S0 S1 hr1 hpre hi1 h4096 h0S1 h3S1 ⟨hl1, hl2, hl3, hl4⟩ (by omega) (by omega) (by omega) h321
    (hHst S1.mem _ _ hi1.2.2.2.2.1 ⟨hl1, hl2, hl3, hl4⟩ hDA1)) ?_
  intro S2 hr2 hq2
  obtain ⟨hi2, r0, r1, r2, e0, e3, e1, hr1l, hr2pos, hr264, hIn, hBH⟩ := hq2
  obtain ⟨hlc, hp48, hacc, hstr, -⟩ := hBH
  obtain ⟨-, -, -, -, -, -, -, hwa2⟩ := finvD_tab hpre hi2
  obtain ⟨r, hr, hrr1, hrr2⟩ := hIn
  have hdis2 := MemFrame.outside_mem hout hr
  refine ReachesRet.mono (wrd_call impl rt stack fW fP fF fWr RWr z tab data ch32 (decBytes (S0.mem.readLE z.toNat 32)) r0 r1 r2 hWr S0 S2 hr2 hpre hi2
    e0 e3 e1 (by omega) hstr (by omega) (fun h => Janus.Arm64.Memory.accessible_sub S2.mem (Janus.Arm64.Memory.accessible_read_of_write _ hacc) (Or.inl rfl) (by omega) (by omega)) hlc hr264 hret47 (by omega)) (fun S' h => ?_)
  obtain ⟨a1, a2, a3, a4, a5, j0, j3, j1, hR⟩ := h
  exact ⟨a1, a2, a3, a4, a5, r0, r1, r2, j0, j3, j1, hR⟩

end Fv256.Amd64.FormatFast
