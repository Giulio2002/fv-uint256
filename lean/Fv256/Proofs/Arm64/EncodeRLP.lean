import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.RlpSpec
import Fv256.Proofs.Common.RlpLemmas
import Fv256.Proofs.Arm64.ErlpCases
import Fv256.Proofs.Arm64.ErlpEJ
import Fv256.Proofs.Arm64.ErlpWit
import Fv256.Proofs.Arm64.ErlpInhabit

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

open Fv256.Arm64.CallSites

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

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/EncodeRLP.lean
def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `X0 = Big`'s type descriptor, `SP = sp0 - 64` (the argument of `H` in `hH`). -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 64), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite H rt 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = tyA := by decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 64 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH tyA (Or.inl rfl)

/-- The call state of the `Write` method (U-WITNESS-CALLSITE): `Write(p)` with `p = (heap, 4, 4)` holding `rlpBytes (*z)` (the bytes `83 01 12 34` written at `heap`),
`X0 = w`, `SP = sp0 - 64`, at the method's entry. -/
def wsWr00 : State := { s0 with mem := s0.mem.writeLE heap 4 0x34120183 }
def wsWr0 : State := { wsWr00 with regs := fun i => if i = 0 then wA else if i = 1 then BitVec.ofNat 64 heap else if i = 2 then 4 else if i = 3 then 4 else s0.regs i }
def wsWr : State := { wsWr0 with sp := BitVec.ofNat 64 (sp0 - 64), pc := BitVec.ofNat 64 A0 }

set_option maxRecDepth 100000 in
theorem wsWr_pre : ICallPre 4 stack 96 rt
    (fun sc => sc.regs 0 = wA ∧
      StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem zA.toNat)) ∧
      (sc.regs 3).toNat = (sc.regs 2).toNat) wsWr := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide, ?_, rfl, ?_, by decide⟩
  · simp only [rt, outside_cons, outside_nil]; decide
  · refine ⟨by decide, by decide, fun _ => by decide, by decide⟩

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
        H [tyOne] (s.regs 28).toNat (s.sp.toNat - 64) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 fn ∧ ICallPre 4 stack 96 rt (fun sc => sc.regs 0 = w ∧ StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧ (sc.regs 3).toNat = (sc.regs 2).toNat) s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 1 = e2) ∧
        (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 64 - stack, s.sp.toNat + 32)]) := by
  refine ⟨impl, rt, H, A0, stack, R0, zA, tabA, wA, retA, s0, hnew, ?w1, hret, setup, pre,
    ⟨wsNew, rfl, wsNew_pre⟩,
    ⟨wsWr, rfl, wsWr_pre⟩,
    correctness impl rt H A0 stack R0 zA tabA wA hnew ?w1 retA hret s0 setup pre⟩
  case w1 => exact hw zA wA
end Witness

end Fv256.Arm64.EncodeRLP
