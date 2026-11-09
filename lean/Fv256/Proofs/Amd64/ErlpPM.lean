import Fv256.Proofs.Amd64.ErlpDefs
import Fv256.Proofs.Common.RlpBytes
import Fv256.Proofs.Amd64.ErlpPMb
import Fv256.Proofs.Amd64.ErlpS1m

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `8 ≤ bitlen`: one `newobject([33]byte)`, the four `BSWAP` stores, the prefix byte, the `Write` -/
theorem erlp_pm (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
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
    (hH2 : H [tyBig] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : (s.regs 4).toNat % 8 = 0) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true) (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl)
    (hJ : EJ z tab w s S bl) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h2, h4, h5, h14, hx, hdf, hfr, hreg, m16, m24, m8⟩ := hJ
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
  janus64_data hd [hwa]
  janus64_run until [Extracted.entry + 0xc9] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfm
  obtain ⟨c8, cr, cz, cbl, c16, c24, cl, cfn, cta, cwa⟩ := erlp_s1m rt s.mem S.mem _ (s.regs 4).toNat stack z.toNat tab.toNat
    w.toNat (s.regs 5).toNat ret bl fn h4104 hwb hout htr hzo hzd htd (by omega) hza hwa hta hfn' hr (by omega) (by omega)
    (by omega) (by omega) hfr m8 m16 m24 _ hfm
  have e56 : (18446744073709551560 + BitVec.toNat (s.regs 4)) % 18446744073709551616 = BitVec.toNat (s.regs 4) - 56 := by
    have := (s.regs 4).isLt; omega
  have hzr := (cl z.toNat 32 (Nat.le_refl _) (Nat.le_refl _)).1
  refine erlp_pmb impl rt fn stack R z tab w ret hret hw s _ h4104 hfn hwb hwn hout htb htr hal hzo hzd hzn hzb bl hbl hb8 hb256
    ?hpc _ ?hreg0 hin ?hob ?hoacc hdj hdz hdt ?hr4 ?hr5 ?hr14 ?hx15 ?hdf ?hm8 ?hmr ?hmz ?hmbl ?hm16 ?hm24
    ?hl0 ?hal0 ?hl1 ?hal1 ?hl2 ?hal2 ?hl3 ?hal3 ?hzr ?hfn ?hta ?hwa ?hF1
  case hr4 => simp [retState64, callRegs64, setRegF]; bv_omega
  case hreg0 => simp [retState64, callRegs64, setRegF]
  case hr5 => simp [retState64, callRegs64, setRegF, h5]
  case hr14 => simp [retState64, callRegs64, setRegF, h14]
  case hx15 => simp [retState64]; exact congrFun hx 15
  case hdf => rfl
  case hpc =>
    simp [retState64, retAddrOf, setRegF]
    simp only [e56, Janus.Arm64.Memory.readLE_writeLE_self]
    rfl
  case hob => omega
  case hoacc =>
    simp only [retState64]
    rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    omega
  case hm8 => simp only [retState64]; exact c8
  case hmr => simp only [retState64]; exact cr
  case hmz => simp only [retState64]; exact cz
  case hmbl => simp only [retState64]; exact cbl
  case hm16 => simp only [retState64]; exact c16
  case hm24 => simp only [retState64]; exact c24
  case hl0 => simp only [retState64]; exact (cl z.toNat 8 (Nat.le_refl _) (off_ok0 _)).1
  case hl1 => simp only [retState64]; exact (cl (z.toNat + 8) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hl2 => simp only [retState64]; exact (cl (z.toNat + 16) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hl3 => simp only [retState64]; exact (cl (z.toNat + 24) 8 (le_off _ _) (off_ok _ _ (by decide))).1
  case hal0 =>
    simp only [retState64]
    rw [(cl z.toNat 8 (Nat.le_refl _) (off_ok0 _)).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (Nat.le_refl _) (off_ok0 _)
  case hal1 =>
    simp only [retState64]
    rw [(cl (z.toNat + 8) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hal2 =>
    simp only [retState64]
    rw [(cl (z.toNat + 16) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hal3 =>
    simp only [retState64]
    rw [(cl (z.toNat + 24) 8 (le_off _ _) (off_ok _ _ (by decide))).2]
    exact Janus.Arm64.Memory.accessible_mono _ hza (le_off _ _) (off_ok _ _ (by decide))
  case hzr => simp only [retState64]; exact hzr
  case hfn => simp only [retState64]; exact cfn
  case hta => simp only [retState64]; exact cta
  case hwa => simp only [retState64]; exact cwa
  case hF1 =>
    simp only [retState64]
    janus_frame

end Fv256.Amd64.EncodeRLP
