import Fv256.Proofs.Arm64.ErlpDefs
import Fv256.Proofs.Common.RlpBytes
import Fv256.Proofs.Common.RlpArm
import Fv256.Proofs.Arm64.ErlpPMb
import Fv256.Proofs.Arm64.ErlpS1m

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

set_option maxRecDepth 100000 in
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
  janus_grab 4096 as hfm
  obtain ⟨c72, c64, cz, cbl, c16, c24, cl, cfn, cta, cwa⟩ := erlp_s1m rt s.mem S.mem _ s.sp.toNat stack z.toNat tab.toNat
    w.toNat (s.regs 29).toNat ret bl fn h4104 hwb hout htr hzo hzd htd (by omega) hwa hta hfn' (by omega) (by omega)
    (by omega) (by omega) hfr m72 m64 m16 m24 hfm
  have hzr := (cl z.toNat 32 (Nat.le_refl _) (Nat.le_refl _)).1
  refine erlp_pmb impl rt fn stack R z tab w ret hret hw s _ h4104 hfn4 hfn hwb hwn hout htb htr hal hzo hzd hzn hzb bl hbl hb8 hb256
    ?hpc _ ?hreg0 hin ?hob ?hoacc hdj hdz hdt ?hsp ?h29 ?h28 ?h18 ?hm72 ?hm64 ?hmz ?hmbl ?hm16 ?hm24
    ?hl0 ?hal0 ?hl1 ?hal1 ?hl2 ?hal2 ?hl3 ?hal3 ?hzr ?hfn ?hta ?hwa ?hF1
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
  case hm72 => simp only [retStateX]; exact c72
  case hm64 => simp only [retStateX]; exact c64
  case hmz => simp only [retStateX]; exact cz
  case hmbl => simp only [retStateX]; exact cbl
  case hm16 => simp only [retStateX]; exact c16
  case hm24 => simp only [retStateX]; exact c24
  case hl0 => simp only [retStateX]; exact (cl z.toNat 8 (Nat.le_refl _) (off_ok0 _)).1
  case hl1 => simp only [retStateX]; exact (cl (z.toNat + 8) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hl2 => simp only [retStateX]; exact (cl (z.toNat + 16) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hl3 => simp only [retStateX]; exact (cl (z.toNat + 24) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hal0 =>
    simp only [retStateX]
    rw [(cl z.toNat 8 (Nat.le_refl _) (off_ok0 _)).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (Nat.le_refl _) (off_ok0 _)
  case hal1 =>
    simp only [retStateX]
    rw [(cl (z.toNat + 8) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hal2 =>
    simp only [retStateX]
    rw [(cl (z.toNat + 16) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hal3 =>
    simp only [retStateX]
    rw [(cl (z.toNat + 24) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hzr => simp only [retStateX]; exact hzr
  case hfn => simp only [retStateX]; exact cfn
  case hta => simp only [retStateX]; exact cta
  case hwa => simp only [retStateX]; exact cwa
  case hF1 =>
    simp only [retStateX]
    janus_frame

end Fv256.Arm64.EncodeRLP
