import Fv256.Proofs.Arm64.ErlpDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `bitlen = 0`: one `newobject([1]byte)`, the byte `0x80`, the `Write` -/
theorem erlp_p0 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
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
    (hH2 : H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : s.sp.toNat % 16 = 0)
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat)
    (hz0 : s.mem.readLE z.toNat 32 = 0)
    (hJ : EJ z tab w ret s S 0) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h3, hsp, h29, h28, h18, hfr, hreg, m16, m24, m72, m64⟩ := hJ
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  janus_eval_nat h_to : tyOne
  rw [h_to] at hH2
  have hH2' := hH2
  rw [← hrv] at hH2'
  janus_data hd [hwa]
  janus_run until [Extracted.entry + 0x1a0] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfn
  have hzr := hfn.readLE z.toNat 32 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  have hz1 : S.mem.readLE z.toNat 32 = 0 := by
    rw [hfr.readLE z.toNat 32 (out_z2 hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))]
    exact hz0
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hz1] at hzr
  janus_run [hfn', m16, m24, m72, m64, rlpVal, hzr, rlpBytes_zero, strBytes_write1] calls [hnew.pos, hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Arm64.EncodeRLP
