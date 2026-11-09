import Fv256.Proofs.Amd64.ErlpP0
import Fv256.Proofs.Amd64.ErlpP1
import Fv256.Proofs.Amd64.ErlpPM

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the three paths from the join `EncodeRLP+0xa0` with `z ≠ nil`, by the bit length of `*z` -/
theorem erlp_cases (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R (WP z w))
    (s S : State) (h4104 : 4104 ≤ stack) (hfn : fn < 2 ^ 47)
    (hwb : 56 + stack ≤ (s.regs 4).toNat) (hwn : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hwa : s.mem.accessible ((s.regs 4).toNat - (56 + stack)) (56 + stack + 32) true = true)
    (hout : Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt) (hfn' : s.mem.readLE (tab.toNat + 24) 8 = fn)
    (hta : s.mem.accessible (tab.toNat + 24) 8 false = true)
    (htd : (tab.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24))
    (hH1 : H [tyBig] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
    (hH2 : H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : (s.regs 4).toNat % 8 = 0) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true)
    (hJ : EJ z tab w s S (Spec.bitLen (s.mem.readLE z.toNat 32))) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  by_cases h0 : Spec.bitLen (s.mem.readLE z.toNat 32) = 0
  · have hv : s.mem.readLE z.toNat 32 = 0 := by
      refine Classical.byContradiction fun h => ?_
      simp [Spec.bitLen, h] at h0
    rw [h0] at hJ
    exact erlp_p0 impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn hwb hwn hwa hout htb htr hfn' hta htd hH2
      hd hal hr hzo hzd hv hJ
  by_cases h7 : Spec.bitLen (s.mem.readLE z.toNat 32) ≤ 7
  · exact erlp_p1 impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn hwb hwn hwa hout htb htr hfn' hta htd hH2
      hd hal hr hzo hzd hzn hzb hza _ rfl h0 h7 hJ
  · exact erlp_pm impl rt H fn stack R z tab w ret hret hnew hw s S h4104 hfn hwb hwn hwa hout htb htr hfn' hta htd hH1
      hd hal hr hzo hzd hzn hzb hza _ rfl (by omega) hJ

end Fv256.Amd64.EncodeRLP
