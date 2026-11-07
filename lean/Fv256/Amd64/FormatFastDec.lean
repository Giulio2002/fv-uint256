import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
import Fv256.Amd64.DecExt
import Fv256.GrabTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast Fv256.E Fv256.Amd64.Dec

namespace Fv256.Amd64.FormatFast

set_option janus.callRegions true in
/-- the `d/v/s` path: `Dec(z)` from `Format+0x139`, return at `Format+0x145` -/
theorem dec_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x139))
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
        (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 384 - 0x58) (rtView rt M)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x145)) S
      (fun S' => FInvD rt stack z tab data ch32 S0 S' ∧
        StrOut S'.mem (S'.regs 0).toNat (S'.regs 3).toNat (decBytes (S0.mem.readLE z.toNat 32)) ∧
        DecAt rt 5163273 5176582 5134938 (S'.regs 0).toNat (S'.regs 3).toNat ∧
        S'.mem.regions = S0.mem.regions ∧ Extracted.program.DataLoaded S'.mem) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0', h3', h1', h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  have hwb0 := hwb
  have hout0 := hout
  have hdlS : Extracted.program.DataLoaded S.mem := by
    refine dataLoaded_frame (m := S0.mem) hdl hreg ifr (fun d hd => ?_)
    have hdj := Fv256.E.dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, trivial⟩ <;> omega
  have hgS : S.mem.readLE ((S0.regs 14).toNat + 16) 8 = S0.mem.readLE ((S0.regs 14).toNat + 16) 8 :=
    ifr.readLE _ _ (out_fl hgo (by omega) hwb)
  have hgaS : S.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true := by rw [ifr.accessible]; exact hg2
  have hvS : S.mem.readLE z.toNat 32 = S0.mem.readLE z.toNat 32 := hzr
  have hH1S : 2 ^ 64 ≤ S0.mem.readLE z.toNat 32 → H [0, (S0.regs 4).toNat - 8 - 376 + 86 + (98 - decLen (S0.mem.readLE z.toNat 32)),
      decLen (S0.mem.readLE z.toNat 32)] (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 376 - 8) (rtView rt S.mem) :=
    hH1 S.mem ifr
  have hH2S : 100 ≤ S0.mem.readLE z.toNat 32 → S0.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (S0.regs 4).toNat - 8 - 384 - 32 + (24 - decLen (S0.mem.readLE z.toNat 32)), decLen (S0.mem.readLE z.toNat 32)]
        (S0.regs 14).toNat ((S0.regs 4).toNat - 8 - 384 - 88) (rtView rt S.mem) :=
    hH2 S.mem ifr
  janus64_run [i50, hwa, hdlS, hgaS, hH1S, hH2S, hvS, hgS] until [Extracted.entry + 0x145] calls [dec_summary_ext impl rt H z hc]
  -- named by content (never positional rename_i): a new conjunct in dec_summary_ext's post must not shift these
  janus_grab 4568 as hfrD
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  have hrip : s'.rip = _ := by assumption
  have h4 : s'.regs 4 = _ := by assumption
  have h5 : s'.regs 5 = _ := by assumption
  have h14 : s'.regs 14 = _ := by assumption
  have hx : s'.xmm 15 = _ := by assumption
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  simp (disch := omega) only [valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hvS] at hl1 hl2 hl3 hl4
  have hSO' : StrOut s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (decBytes (S0.mem.readLE z.toNat 32)) :=
    ⟨hl1, hl2, fun h => by rw [hfrD.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; rw [ifr.accessible]; exact hl3 h, hl4⟩
  have hfin : FInvD rt stack z tab data ch32 S0 s' :=
    finvD_call1 hi'.toD hwb0 hout0 h4568 hfrD (by simp [setRegF_apply, h4, i4, sub_add8])
      (by simp [setRegF_apply, h5]) (by simp [setRegF_apply, h14]) (by simp [hx]) rfl
  refine ReachesRet.done ?_ ⟨hfin, hSO', hDA, hrg1.trans hreg, ?_⟩
  · rw [hrip]
    simp (disch := omega) only [retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8, Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · refine dataLoaded_frame (m := S0.mem) hdl (hrg1.trans hreg) hfin.2.2.2.2.1 (fun d hd => ?_)
    have hdj := Fv256.E.dataLoaded_disjoint hdl hd hwa0
    simp only [FL, outside_append, outside_cons, outside_nil]
    refine ⟨hdrt d hd, ?_, ?_, trivial⟩ <;> omega

end Fv256.Amd64.FormatFast
