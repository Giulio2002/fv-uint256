import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.DecExt
import Fv256.GrabTac
import Fv256.GrabEq

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.E Fv256.Arm64.Dec

namespace Fv256.Arm64.FormatFast

set_option janus.callRegions true in
/-- the `d/v/s` path: `Dec(z)` from `Format+0x144`, return at `Format+0x14c` -/
theorem dec_call (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x144))
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
        (S0.regs 28).toNat (S0.sp.toNat - 384 - 96) (rtView rt M)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x14c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧
        StrOut S'.mem (S'.regs 0).toNat (S'.regs 1).toNat (decBytes (val256 S0.mem z.toNat)) ∧
        DecAt rt 989280 1002589 960826 (S'.regs 0).toNat (S'.regs 1).toNat ∧
        S'.mem.regions = S0.mem.regions ∧ Extracted.program.DataLoaded S'.mem) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  have hdlS : Extracted.program.DataLoaded S.mem := by
    refine dataLoaded_frame (m := S0.mem) hdl hreg ifr (fun d hd => ?_)
    have hdj := dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, ?_, trivial⟩ <;> omega
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hgS : S.mem.readLE ((S0.regs 28).toNat + 16) 8 = S0.mem.readLE ((S0.regs 28).toNat + 16) 8 :=
    ifr.readLE _ _ (out_fl hgo (by omega) hwb)
  have hgaS : S.mem.accessible ((S0.regs 28).toNat + 16) 8 false = true := by rw [ifr.accessible]; exact hg2
  have hH1S : 2 ^ 64 ≤ val256 S0.mem z.toNat →
      H [0, S0.sp.toNat - 384 + 94 + (98 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384) (rtView rt S.mem) := hH1 S.mem ifr
  have hH2S : 100 ≤ val256 S0.mem z.toNat → val256 S0.mem z.toNat < 2 ^ 64 →
      H [0, S0.sp.toNat - 384 - 32 + (24 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384 - 96) (rtView rt S.mem) := hH2 S.mem ifr
  have hvS : val256 S.mem z.toNat = val256 S0.mem z.toNat := hzr
  simp only [Spec.val256_limbs] at hH1S hH2S
  have hout8 : Outside (S0.sp.toNat - 4608) (4608 + 8) rt := hout.of_sub (by omega) (by omega)
  janus_run [i88, hwa, hdlS, hgaS, hH1S, hH2S, hvS, hgS, i4, i28] until [Extracted.entry + 0x14c] calls [dec_summary_ext impl rt H z hc]
  -- named by content (never positional rename_i): a new conjunct in dec_summary_ext's post must not shift these
  grab_frame_last 4608 as hfrD
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  grab_eq s' pc as hrip
  grab_eq s' sp as h4
  grab_eq s' regs 29 as h29
  grab_eq s' regs 28 as h28
  grab_eq s' regs 18 as h18
  clear_frame_imps
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  rw [← Spec.val256_limbs S0.mem z.toNat] at hl1 hl4
  have hSO' : StrOut s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (decBytes (val256 S0.mem z.toNat)) :=
    ⟨hl1, hl2, fun h => by rw [hfrD.accessible, ifr.accessible]; exact hl3 h, hl4⟩
  have hfin : FInv rt stack z tab data ch32 S0 s' :=
    finv_call1 hi' hst hout (k := 4608) h4608 hfrD (by simp [h4, i4, setReg_apply]) (by simp [h29, i29, setReg_apply]) (by simp [h28, i28, setReg_apply])
      (by simp [h18, i18, setReg_apply]) rfl
  refine ReachesRet.done ?_ ⟨hfin, hSO', hDA, hrg1.trans hreg, ?_⟩
  · simp [hrip, Extracted.entry, setReg_apply]
  · refine dataLoaded_frame (m := S0.mem) hdl (hrg1.trans hreg) hfin.2.2.2.2.1 (fun d hd => ?_)
    have hdj := dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, ?_, trivial⟩ <;> omega

end Fv256.Arm64.FormatFast
