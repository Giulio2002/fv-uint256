import Fv256.Proofs.Arm64.ErlpDefs
import Fv256.Proofs.Arm64.ErlpP1b

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `1 ≤ bitlen ≤ 7`: one `newobject([1]byte)`, the byte `z[0]`, the `Write` -/
theorem erlp_p1 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
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
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true)
    (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb1 : bl ≠ 0) (hb7 : bl ≤ 7)
    (hJ : EJ z tab w ret s S bl) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h3, hsp, h29, h28, h18, hfr, hreg, m16, m24, m72, m64⟩ := hJ
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  have hv0 : s.mem.readLE z.toNat 32 ≠ 0 := fun h => by simp [Spec.bitLen, h] at hbl; omega
  have hv7 := bitLen_le7_lt _ hv0 (by omega)
  have hv8 : s.mem.readLE z.toNat 8 = s.mem.readLE z.toNat 32 := by
    have := Janus.Arm64.Memory.readLE_mod s.mem z.toNat 32 8 (by omega)
    omega
  have hrb := rlpBytes_small _ hv0 (by omega)
  have hS8 : S.mem.readLE z.toNat 8 = s.mem.readLE z.toNat 8 :=
    hfr.readLE z.toNat 8 (out_z2 hzd h4104 hwb (Nat.le_refl _) (off_ok0 _))
  have hS32 : S.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 :=
    hfr.readLE z.toNat 32 (out_z2 hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  janus_eval_nat h_to : tyOne
  rw [h_to] at hH2
  rw [← hrv] at hH2
  janus_data hd [hwa]
  janus_run until [Extracted.entry + 0x150] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfm
  have hzr := hfm.readLE z.toNat 32 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  have hzr8 := hfm.readLE z.toNat 8 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (off_ok0 _))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hS8, hS32] at hzr hzr8
  have hza8 : s.mem.accessible z.toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (Nat.le_refl _) (off_ok0 _)
  have hzacc := hfm.accessible z.toNat 8 false
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hza8] at hzacc
  have hmod : s.mem.readLE z.toNat 32 % 256 = s.mem.readLE z.toNat 32 := Nat.mod_eq_of_lt (by omega)
  refine erlp_p1b impl rt fn stack R z tab w ret hret hw s _ h4104 hfn4 hfn hwb hwn hout htb htr hal hzo hzd hzn hzb
    (s.mem.readLE z.toNat 32) hv7 hrb ?hpc _ ?hreg0 hin ?hob ?hoacc hdj hdz hdt ?hsp ?h29 ?h28 ?h18 ?hm72 ?hm64 ?hmz ?hm16
    ?hm24 ?hz8 ?hz32 ?hzacc ?hfn ?hta ?hwa ?hF1
  case hpc => simp [retStateX, callRegs, setReg]; rfl
  case hreg0 => simp [retStateX, callRegs, setReg]
  case hsp => simp [retStateX]
  case h29 => simp [retStateX, callRegs, setReg, h29]
  case h28 => simp [retStateX, callRegs, setReg, h28]
  case h18 => simp [retStateX, callRegs, setReg, h18]
  case hob => omega
  case hoacc =>
    simp only [retStateX]
    rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    omega
  case hm72 =>
    simp only [retStateX]
    rw [hfm.readLE (s.sp.toNat - 72) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inl (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m72
  case hm64 =>
    simp only [retStateX]
    rw [hfm.readLE (s.sp.toNat - 64) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inl (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m64
  case hmz =>
    simp only [retStateX]
    rw [hfm.readLE (s.sp.toNat + 8) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    have : z.toNat < 2 ^ 64 := z.isLt
    omega
  case hm16 =>
    simp only [retStateX]
    rw [hfm.readLE (s.sp.toNat + 16) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m16
  case hm24 =>
    simp only [retStateX]
    rw [hfm.readLE (s.sp.toNat + 24) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m24
  case hz8 => simp only [retStateX]; rw [hzr8, hv8]
  case hz32 => simp only [retStateX]; exact hzr
  case hzacc => simp only [retStateX]; exact hzacc
  case hfn =>
    simp only [retStateX]
    rw [hfm.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil]
      refine ⟨htr, ?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)]
    exact hfn'
  case hta =>
    simp only [retStateX]
    rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    exact hta
  case hwa =>
    simp only [retStateX]
    rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    exact hwa
  case hF1 =>
    simp only [retStateX]
    janus_frame

end Fv256.Arm64.EncodeRLP
