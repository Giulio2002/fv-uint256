import Fv256.Amd64.SfdTopG

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd
  Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg Fv256.Amd64.SfdTopBr

namespace Fv256.Amd64.SfdTop

theorem topSt_of_callSt {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {z pS : BitVec 64}
    {s Sc S2 : State} (hL : R2.Laws) (hC : CallSt R R2 T b L lo hi z pS s Sc)
    (h4 : S2.regs 4 = s.regs 4 - 64#64) (h5 : S2.regs 5 = Sc.regs 5) (h14 : S2.regs 14 = Sc.regs 14)
    (hx : S2.xmm 15 = Sc.xmm 15) (hdf : S2.df = Sc.df) (hfs : S2.fsBase = Sc.fsBase)
    (hf : MemFrame Sc.mem S2.mem [(lo, hi)]) (hw : lo + 32 ≤ hi) (hlo : lo + 72 ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 8 ≤ hi)
    (hsp : (s.regs 4).toNat < 2 ^ 64)
    (e1 : S2.mem.readLE ((s.regs 4).toNat - 8) 8 = Sc.mem.readLE ((s.regs 4).toNat - 8) 8)
    (e2 : S2.mem.readLE ((s.regs 4).toNat + 8) 8 = Sc.mem.readLE ((s.regs 4).toNat + 8) 8)
    (e3 : S2.mem.readLE ((s.regs 4).toNat + 16) 8 = Sc.mem.readLE ((s.regs 4).toNat + 16) 8)
    (e4 : S2.mem.readLE (s.regs 4).toNat 8 = Sc.mem.readLE (s.regs 4).toNat 8) :
    TopSt R R2 T b L lo hi z pS s S2 := by
  obtain ⟨a4, a5, a14, ax, adf, afs, amf, abp, az, ap, aret, aenv⟩ := hC
  have hs64 : (S2.regs 4).toNat = (s.regs 4).toNat - 64 := by rw [h4]; exact bv_sub_c _ 64 (by decide) (by omega)
  have hEnv := aenv
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ := aenv
  have hs72 : (Sc.regs 4).toNat = (s.regs 4).toNat - 72 := by rw [a4]; exact bv_sub_c _ 72 (by decide) (by omega)
  refine ⟨h4, h5.trans a5, h14.trans a14, hx.trans ax, hdf.trans adf, hfs.trans afs, ?_, e1.trans abp, e2.trans az, e3.trans ap,
    e4.trans aret, ?_⟩
  · exact MemFrame.trans amf hf (fun a n h => ⟨h, h⟩)
  · exact Env.frame0 hL hEnv ⟨by rw [hs64]; omega, by rw [hs64]; omega, by rw [hs64]; omega⟩ h14 hf hw

end Fv256.Amd64.SfdTop
