import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.DecExt
import Fv256.Arm64.FormatFastDec
import Fv256.Arm64.FormatFastDecStr
import Fv256.Arm64.FormatFastStb
import Fv256.Arm64.FormatFastWr

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.E Fv256.Arm64.Dec

namespace Fv256.Arm64.FormatFast

/-- the `d`, `v`, `s` path from `Format+0x144` to the return: `Dec(z)`, `stringtoslicebyte`, one `Write` of `decBytes v`, epilogue -/
theorem dec_path (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat) (RWr : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State)
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
      (FastWP data (decBytes (val256 S0.mem z.toNat))))
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x144))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4608 : 4608 ≤ stack) (hreg : S.mem.regions = S0.mem.regions)
    (hdl : Extracted.program.DataLoaded S0.mem) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (ht1 : Outside 989280 256 rt) (ht2 : Outside 1002589 256 rt)
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
    (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S
      (fun S' => S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
        S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
        MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
        (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) := by
  have hpre0 := hpre
  obtain ⟨-, -, -, -, -, -, hwb, -, hwa0, hout, -⟩ := hpre0
  refine rr_trans (dec_call impl rt H stack fW fP fF fWr z tab data ch32 hc S0 S hpc hpre hi h4608 hreg hdl hdrt ht1 ht2 hg hgo hgd hH1 hH2) ?_
  intro S1 hr1 hq1
  obtain ⟨hi1, hso1, hDA1, hreg1, hdl1⟩ := hq1
  obtain ⟨-, -, -, -, -, -, -, hwa1⟩ := finv_tab hpre hi1
  obtain ⟨hdis1, h321⟩ := dec_str_out hdl1 hwa1 hout hrt32 hDA1
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hso1
  have hv256 : val256 S0.mem z.toNat < 2 ^ 256 := by simpa [val256] using Janus.Arm64.Memory.readLE_lt S0.mem z.toNat 32
  have hd78 : decLen (val256 S0.mem z.toNat) ≤ 78 :=
    decLen_le_of_lt_pow _ 78 (by omega) (Nat.lt_of_lt_of_le hv256 (by decide))
  have hd1 := decLen_pos (val256 S0.mem z.toNat)
  have hlenE : (decBytes (val256 S0.mem z.toNat)).length = decLen (val256 S0.mem z.toNat) := rfl
  have h0S1 : S1.regs 0 = BitVec.ofNat 64 (S1.regs 0).toNat := by simp
  have h1S1 : S1.regs 1 = BitVec.ofNat 64 (S1.regs 1).toNat := by simp
  refine rr_trans (stb_dec impl rt H stack fW fP fF fWr z tab data ch32 (decBytes (val256 S0.mem z.toNat))
    (S1.regs 0).toNat (S1.regs 1).toNat hc2 S0 S1 hr1 hpre hi1 (by omega) h0S1 h1S1 ⟨hl1, hl2, hl3, hl4⟩ (by omega)
    (by omega) (by omega) h321
    (hHst S1.mem _ _ hi1.2.2.2.2.1 ⟨hl1, hl2, hl3, hl4⟩ hDA1)) ?_
  intro S2 hr2 hq2
  obtain ⟨hi2, r0, r1, r2, e0, e1, e2, hr1l, hr2pos, hr264, hIn, hBH⟩ := hq2
  obtain ⟨hlc, hp48, hacc, hstr, -⟩ := hBH
  obtain ⟨-, -, -, -, -, -, -, hwa2⟩ := finv_tab hpre hi2
  obtain ⟨r, hr, hrr1, hrr2⟩ := hIn
  have hdis2 := MemFrame.outside_mem hout hr
  refine rr_mono (wrd_call impl rt stack fW fP fF fWr RWr z tab data ch32 (decBytes (val256 S0.mem z.toNat)) r0 r1 r2 hWr S0 S2 hr2 hpre hi2
    e0 e1 e2 (by omega) hstr (by omega) (fun h => Janus.Arm64.Memory.accessible_sub S2.mem (Janus.Arm64.Memory.accessible_read_of_write _ hacc) (Or.inl rfl) (by omega) (by omega)) hlc hr264 (by omega) hret) (fun S' h => ?_)
  obtain ⟨a1, a2, a3, a4, a5, j0, j1, j2, hR⟩ := h
  exact ⟨a1, a2, a3, a4, a5, r0, r1, r2, j0, j1, j2, hR⟩

end Fv256.Arm64.FormatFast
