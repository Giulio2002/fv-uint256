import Fv256.Arm64.ErlpDefs
import Fv256.RlpBytes
import Fv256.RlpArm

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
/-- the path `8 ≤ bitlen`: one `newobject([33]byte)`, the four `REV` stores, the prefix byte, the `Write` -/
theorem erlp_pm (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
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
    (hH2 : H [tyBig] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : s.sp.toNat % 16 = 0)
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true)
    (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl)
    (hJ : EJ z tab w ret s S bl) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h3, hsp, h29, h28, h18, hfr, hreg, m16, m24, m72, m64⟩ := hJ
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  janus_eval_nat h_tb : tyBig
  rw [h_tb] at hH2
  rw [← hrv] at hH2
  have hb256 : bl ≤ 256 := by
    rw [← hbl]
    exact bitLen_le_256 _ (by simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32)
  have hb0 : bl ≠ 0 := by omega
  have hb7 : ¬ bl ≤ 7 := by omega
  have hb7' : ¬ ((bl : Int) ≤ 7) := by omega
  janus_data hd [hwa]
  janus_run until [Extracted.entry + 0xa8] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfn
  have hzr := hfn.readLE z.toNat 32 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  have hr0 := hfn.readLE (z.toNat) 8 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (off_ok0 _))
  have hs0 : S.mem.readLE (z.toNat) 8 = s.mem.readLE (z.toNat) 8 :=
    hfr.readLE _ _ (out_z2 hzd h4104 hwb (Nat.le_refl _) (off_ok0 _))
  have ha0 := hfn.accessible (z.toNat) 8 false
  have hb0 : s.mem.accessible (z.toNat) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (Nat.le_refl _) (off_ok0 _)
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hs0] at hr0
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hb0] at ha0
  have hr1 := hfn.readLE (z.toNat + 8) 8 (out_z hzo hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have hs1 : S.mem.readLE (z.toNat + 8) 8 = s.mem.readLE (z.toNat + 8) 8 :=
    hfr.readLE _ _ (out_z2 hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have ha1 := hfn.accessible (z.toNat + 8) 8 false
  have hb1 : s.mem.accessible (z.toNat + 8) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hs1] at hr1
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hb1] at ha1
  have hr2 := hfn.readLE (z.toNat + 16) 8 (out_z hzo hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have hs2 : S.mem.readLE (z.toNat + 16) 8 = s.mem.readLE (z.toNat + 16) 8 :=
    hfr.readLE _ _ (out_z2 hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have ha2 := hfn.accessible (z.toNat + 16) 8 false
  have hb2 : s.mem.accessible (z.toNat + 16) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hs2] at hr2
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hb2] at ha2
  have hr3 := hfn.readLE (z.toNat + 24) 8 (out_z hzo hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have hs3 : S.mem.readLE (z.toNat + 24) 8 = s.mem.readLE (z.toNat + 24) 8 :=
    hfr.readLE _ _ (out_z2 hzd h4104 hwb (le_off _ _) (off_ok _ _ (by decide)))
  have ha3 := hfn.accessible (z.toNat + 24) 8 false
  have hb3 : s.mem.accessible (z.toNat + 24) 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hs3] at hr3
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hb3] at ha3
  have hS32 : S.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 :=
    hfr.readLE z.toNat 32 (out_z2 hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hS32] at hzr
  have hStr := fun (m : Memory) (obj : Nat) => pm_strA4 m obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
    (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) (s.mem.readLE z.toNat 32) bl
    (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
    (Util.readLE_32 s.mem z.toNat) hbl (by omega) hb256
  have hDA := (arm_arith bl (by omega) hb256).1
  have hnorm := arm_norm bl (by omega) hb256
  have hlenB := pm_lenB (s.mem.readLE z.toNat 32) bl hbl (by omega)
  janus_run [hfn', m16, m24, m72, m64, rlpVal, hzr, hr0, hr1, hr2, hr3, ha0, ha1, ha2, ha3, hzn, hDA, hnorm.1, hnorm.2, hlenB, hStr]
    calls [hnew.pos, hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Arm64.EncodeRLP
