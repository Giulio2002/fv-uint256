import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RlpSpec
import Fv256.Amd64.ErlpCases
import Fv256.Amd64.ErlpEJ
import Fv256.Amd64.ErlpWit

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 7).toNat = (sc.regs 1).toNat)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, w]
      (fun s => 4104 ≤ stack ∧ fn < 2 ^ 47 ∧
        StackGuardOK s 0 ∧ StackWritable s (56 + stack) 32 ∧ SPAligned s ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt ∧
        (z = 0 ∨ (Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat))) ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ Outside (tab.toNat + 24) 8 rt ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        H [tyBig] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem) ∧
        H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
      (fun s s' => (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2) ∧
        (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)])) := by
  intro ret hret s hs ⟨h4104, hfn, hg, hw0, hal, hd, hout, hz, htb, htw, hta, htr, hfn', hH1, hH2⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw0
  simp only [regSP, regG, stackguard0Offset, stackguard0, SPAligned] at hgl hgb hnw2 hgr hwb hwn hwa hal hout hz htb hH1 hH2
  janus_eval_nat h_tb : tyBig
  janus_eval_nat h_to : tyOne
  rw [h_tb] at hH1
  rw [h_to] at hH2
  janus64_data hd [hwa]
  by_cases hz0 : z = 0
  · subst hz0
    janus64_run until [Extracted.entry + 0x1df] calls [hnew.pos, hw]
    janus_grab InRanges as hin0
    have hdj := InRanges.disjoint hin0 hout
    have hdt := InRanges.disjoint hin0 htr
    janus64_run [rlpVal_zero, rlpVal_zero_bv, rlpBytes_zero, strBytes_write1] calls [hnew.pos, hw]
    refine ⟨?_, fun h => h.elim, ?_⟩
    · exact ⟨_, _, _, _, _, _, by janus_assumption_reducible, rfl, rfl⟩
    · janus_frame
  · obtain ⟨⟨hzn, hza⟩, hzo, hzd⟩ := hz.resolve_left hz0
    have hzne : ¬ z.toNat = 0 := fun h => hz0 (BitVec.eq_of_toNat_eq (by simpa using h))
    have x0 := Util.readLE8_lt s.mem z.toNat
    have x1 := Util.readLE8_lt s.mem (z.toNat + 8)
    have x2 := Util.readLE8_lt s.mem (z.toNat + 16)
    have x3 := Util.readLE8_lt s.mem (z.toNat + 24)
    have c0 := Util.clz_bl 64 _ x0
    have c1 := Util.clz_bl 64 _ x1
    have c2 := Util.clz_bl 64 _ x2
    have c3 := Util.clz_bl 64 _ x3
    janus64_run until [Extracted.entry + 0xa0]
    all_goals (
      refine erlp_cases impl rt H fn stack R z tab w ret hret hnew hw s _ h4104 hfn hwb hwn hwa hout htw htr hfn' hta htb hH1 hH2
        hd hal h_ret hzo hzd hzne hzn hza ?_
      refine ej_of rfl ?_ ?_ rfl rfl rfl rfl ?_ rfl (by omega) (by omega)
      · exact h_a0
      · apply BitVec.eq_of_toNat_eq
        have z0 : s.mem.readLE (z.toNat) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have nz0 : s.mem.readLE (z.toNat) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat) 8) := fun h => by simp [Spec.bitLen, h]
        have z1 : s.mem.readLE (z.toNat + 8) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have nz1 : s.mem.readLE (z.toNat + 8) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) := fun h => by simp [Spec.bitLen, h]
        have z2 : s.mem.readLE (z.toNat + 16) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have nz2 : s.mem.readLE (z.toNat + 16) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) := fun h => by simp [Spec.bitLen, h]
        have z3 : s.mem.readLE (z.toNat + 24) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have nz3 : s.mem.readLE (z.toNat + 24) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) := fun h => by simp [Spec.bitLen, h]
        rw [Util.readLE_32, Util.bl_4 _ _ _ _ x0 x1 x2]
        simp only [setRegF, Nat.reduceEqDiff, ite_false, ite_true, if_false, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod, ne_eq]
        (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod]) <;> first | omega | (trace_state; sorry)
      · first | rfl | simp [h_df])

namespace Witness

/-- **Non-vacuity**: the toy allocator, the toy writer (`(len, nil)`), and a concrete call state (`*z = 0x011234`, 17 bits: the
multi-byte path) meet every hypothesis of `correctness`, contracts included. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 7).toNat = (sc.regs 1).toNat) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, w] s ∧
    (4104 ≤ stack ∧ fn < 2 ^ 47 ∧
        StackGuardOK s 0 ∧ StackWritable s (56 + stack) 32 ∧ SPAligned s ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt ∧
        (z = 0 ∨ (Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
          (z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat))) ∧
        (tab.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24) ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ Outside (tab.toNat + 24) 8 rt ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        H [tyBig] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem) ∧
        H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem)) :=
  ⟨impl, rt, H, A0, stack, R0, zA, tabA, wA, retA, s0, hnew, hw zA wA, hret, setup, pre⟩

end Witness

end Fv256.Amd64.EncodeRLP
