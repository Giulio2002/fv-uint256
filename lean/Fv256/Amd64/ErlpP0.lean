import Fv256.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `bitlen = 0` (`z ≠ 0` is impossible here unless `z = 0` in memory): one `newobject([1]byte)`, the byte `0x80`, the `Write` -/
theorem erlp_p0 (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
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
    (hH2 : H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : (s.regs 4).toNat % 8 = 0) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hz0 : s.mem.readLE z.toNat 32 = 0)
    (hJ : EJ z tab w s S 0) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h2, h4, h5, h14, hx, hdf, hfr, hreg, m16, m24, m8⟩ := hJ
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  janus_eval_nat h_to : tyOne
  rw [h_to] at hH2
  rw [← hrv] at hH2
  janus64_data hd [hwa]
  janus64_run until [Extracted.entry + 0x1a6] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfn
  have hzr := hfn.readLE z.toNat 32 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  have hz1 : S.mem.readLE z.toNat 32 = 0 := by
    rw [hfr.readLE z.toNat 32 (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)]
    exact hz0
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hz1] at hzr
  janus64_run [rlpVal, hzr, rlpBytes_zero, strBytes_write1] calls [hnew.pos, hw]
  refine ⟨?_, ?_⟩
  · simp only [hx]
  · apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
    · apply epost_ex
      · assumption
      · rfl
      · rfl
    · janus_frame

end Fv256.Amd64.EncodeRLP
