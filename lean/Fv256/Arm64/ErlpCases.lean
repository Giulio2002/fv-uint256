import Fv256.Arm64.ErlpP0
import Fv256.Arm64.ErlpP1
import Fv256.Arm64.ErlpPM

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the three paths from the join `EncodeRLP+0x88` with `z ≠ nil`, by the bit length of `*z` -/
theorem erlp_cases (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R (WP z w))
    (s S : State) (h4104 : 4104 ≤ stack) (hfn4 : fn % 4 = 0) (hfn : fn < 2 ^ 56)
    (hwb : 64 + stack ≤ s.sp.toNat) (hwn : s.sp.toNat + 32 ≤ 2 ^ 48)
    (hwa : s.mem.accessible (s.sp.toNat - (64 + stack)) (64 + stack + 32) true = true)
    (hout : Outside (s.sp.toNat - 64 - stack) (stack + 96) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt) (hfn' : s.mem.readLE (tab.toNat + 24) 8 = fn)
    (hta : s.mem.accessible (tab.toNat + 24) 8 false = true)
    (htd : tab.toNat + 24 + 8 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ tab.toNat + 24)
    (hH1 : H [tyBig] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
    (hH2 : H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : s.sp.toNat % 16 = 0)
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true)
    (hJ : EJ z tab w ret s S (Spec.bitLen (s.mem.readLE z.toNat 32))) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  by_cases h0 : Spec.bitLen (s.mem.readLE z.toNat 32) = 0
  · have hv : s.mem.readLE z.toNat 32 = 0 := by
      refine Classical.byContradiction fun h => ?_
      simp [Spec.bitLen, h] at h0
    rw [h0] at hJ
    exact erlp_p0 impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn4 hfn hwb hwn hwa hout htb htr hfn' hta htd hH2
      hd hal hzo hzd hv hJ
  by_cases h7 : Spec.bitLen (s.mem.readLE z.toNat 32) ≤ 7
  · exact erlp_p1 impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn4 hfn hwb hwn hwa hout htb htr hfn' hta htd hH2
      hd hal hzo hzd hzn hzb hza _ rfl h0 h7 hJ
  · exact erlp_pm impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn4 hfn hwb hwn hwa hout htb htr hfn' hta htd hH1
      hd hal hzo hzd hzn hzb hza _ rfl (by omega) hJ

end Fv256.Arm64.EncodeRLP
