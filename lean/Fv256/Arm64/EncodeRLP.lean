import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RlpSpec
import Fv256.RlpLemmas
import Fv256.Arm64.ErlpCases
import Fv256.Arm64.ErlpEJ
import Fv256.Arm64.ErlpWit
import Fv256.Arm64.ErlpInhabit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 3).toNat = (sc.regs 2).toNat)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, w]
      (fun s => 4104 ≤ stack ∧ CodePtrOK fn ∧ GuardOK s 0 ∧ StackOK s (64 + stack) 32 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 64 - stack) (stack + 96) rt ∧
        (z = 0 ∨ (Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 64 - stack) (stack + 96))) ∧
        Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 64 - stack) (stack + 96) ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ Outside (tab.toNat + 24) 8 rt ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        H [tyBig] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem) ∧
        H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem))
      (fun s s' => (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2) ∧
        (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)])) := by
  intro ret hret s hs ⟨h4104, ⟨hfn4, hfn⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hwb, hwn, hwa⟩, hd, hout, hz, htd, htb, hta, htr, hfn', hH1, hH2⟩
  janus_intro hs
  janus_eval_nat h_tb : tyBig
  janus_eval_nat h_to : tyOne
  rw [h_tb] at hH1
  rw [h_to] at hH2
  janus_data hd [hwa]
  simp only [Disjoint] at htd
  by_cases hz0 : z = 0
  · subst hz0
    janus_run until [Extracted.entry + 0x1ec] calls [hnew.pos, hw]
    janus_grab InRanges as hin0
    have hdj := InRanges.disjoint hin0 hout
    have hdt := InRanges.disjoint hin0 htr
    janus_run [hfn', rlpVal_zero, rlpVal_zero_bv, rlpBytes_zero, strBytes_write1] calls [hnew.pos, hw]
    refine ⟨?_, fun h => h.elim, ?_⟩
    · exact ⟨_, _, _, _, _, _, by janus_assumption_reducible, rfl, rfl⟩
    · janus_frame
  · obtain ⟨⟨hza, hzb⟩, hzo, hzd⟩ := hz.resolve_left hz0
    have hzne : ¬ z.toNat = 0 := fun h => hz0 (BitVec.eq_of_toNat_eq (by simpa using h))
    simp only [Disjoint] at hzd
    have x0 := Util.readLE8_lt s.mem z.toNat
    have x1 := Util.readLE8_lt s.mem (z.toNat + 8)
    have x2 := Util.readLE8_lt s.mem (z.toNat + 16)
    have x3 := Util.readLE8_lt s.mem (z.toNat + 24)
    have c0 := Util.clz_bl 64 _ x0
    have c1 := Util.clz_bl 64 _ x1
    have c2 := Util.clz_bl 64 _ x2
    have c3 := Util.clz_bl 64 _ x3
    janus_run until [Extracted.entry + 0x88]
    all_goals (
      refine erlp_cases impl rt H fn stack R z tab w ret hret hnew hw s _ h4104 hfn4 hfn hwb hwn hwa hout htb htr hfn' hta htd hH1 hH2
        hd hal hzo hzd hzne hzb hza ?_
      have hr48 := hret.user
      refine ej_of rfl ?_ ?_ rfl rfl rfl rfl rfl (by omega) (by omega) (by omega)
      · exact h_x0
      · apply BitVec.eq_of_toNat_eq
        have z0 : s.mem.readLE z.toNat 8 = 0 → Spec.bitLen (s.mem.readLE z.toNat 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have z1 : s.mem.readLE (z.toNat + 8) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have z2 : s.mem.readLE (z.toNat + 16) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have z3 : s.mem.readLE (z.toNat + 24) 8 = 0 → Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) = 0 := fun h => by simp [Spec.bitLen, h]
        have nz0 : s.mem.readLE z.toNat 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE z.toNat 8) := fun h => by simp [Spec.bitLen, h]
        have nz1 : s.mem.readLE (z.toNat + 8) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) := fun h => by simp [Spec.bitLen, h]
        have nz2 : s.mem.readLE (z.toNat + 16) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) := fun h => by simp [Spec.bitLen, h]
        have nz3 : s.mem.readLE (z.toNat + 24) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) := fun h => by simp [Spec.bitLen, h]
        rw [Util.readLE_32, Util.bl_4 _ _ _ _ x0 x1 x2]
        simp only [setReg, Nat.reduceEqDiff, ite_false, ite_true, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add,
          Nat.reducePow, Nat.reduceMod, ne_eq]
        (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod]) <;>
          omega)

namespace Witness

/-- **Non-vacuity**: the toy allocator, the toy writer (`(len, nil)`), and a concrete call state (`*z = 0x011234`, 17 bits: the
multi-byte path) meet every hypothesis of `correctness`, contracts included. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 3).toNat = (sc.regs 2).toNat) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, w] s ∧
    (4104 ≤ stack ∧ CodePtrOK fn ∧ GuardOK s 0 ∧ StackOK s (64 + stack) 32 ∧
        Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 64 - stack) (stack + 96) rt ∧
        (z = 0 ∨ (Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 64 - stack) (stack + 96))) ∧
        Disjoint (tab.toNat + 24) 8 (s.sp.toNat - 64 - stack) (stack + 96) ∧
        tab.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 24) 8 false = true ∧ Outside (tab.toNat + 24) 8 rt ∧
        s.mem.readLE (tab.toNat + 24) 8 = fn ∧
        H [tyBig] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem) ∧
        H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)) :=
  ⟨impl, rt, H, A0, stack, R0, zA, tabA, wA, retA, s0, hnew, hw zA wA, hret, setup, pre⟩

end Witness

end Fv256.Arm64.EncodeRLP
