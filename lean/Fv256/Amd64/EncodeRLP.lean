import Fv256.Amd64.CallSites.Live
import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.RlpSpec
import Fv256.Amd64.ErlpCases
import Fv256.Amd64.ErlpEJ
import Fv256.Amd64.ErlpWit
import Fv256.Amd64.ErlpInhabit
import Fv256.Amd64.CallSites.Base

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
        (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod]) <;> omega
      · first | rfl | simp [h_df])

namespace Witness

open Fv256.Inhab

open Fv256.CallSites

/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `s0`'s memory at the allocator's entry, `RSP` at the call frame
(`s0`'s `RSP` less 56), `RAX` the `big.Int` type descriptor. -/
def csNew : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 cA, regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 4 then s0.regs 4 - 56#64 else s0.regs i }

theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr]; rfl

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectSite H rt 4096 csNew := by
  have ht : (csNew.regs 0).toNat = tyA := by decide
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  show H [(csNew.regs 0).toNat] _ _ (rtView rt s0.mem)
  rw [ht]; exact hH tyA (Or.inl rfl)

/-- The call state of the writer (U-WITNESS-CALLSITE): at `A0`, with `RAX = w`, the encoding of `*z` (`0x80` for `z`'s zero cell)
at `0x2000`, flat memory, `RSP = 2^40`. -/
def csW : Amd64.State := callSt64At (BitVec.ofNat 64 A0) wA 1 0x2000 0 1 (strMem [0x80] 0x2000)

theorem csW_pre : ICallPre64 4 stack 56 rt
    (fun sc => sc.regs 0 = wA ∧ StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem zA.toNat)) ∧
      (sc.regs 7).toNat = (sc.regs 1).toNat) csW := by
  have h0 : rlpBytes (rlpVal (strMem [0x80] 0x2000) zA.toNat) = [0x80] := by
    have : (strMem [0x80] 0x2000).readLE zA.toNat 32 = 0 := readLE_strMem_far _ _ _ _ (by simp [zA, zp])
    simp [rlpVal, rlpBytes, this, zA, zp]
  have hret : (strMem [0x80] 0x2000).readLE (2 ^ 40) 8 < 2 ^ 47 := by
    rw [readLE_strMem_far _ _ _ _ (by simp)]; omega
  refine callSt64At_pre (by rfl) hret (by decide) (by omega) (by omega) ?_ ?_
  · simp only [rt, outside_cons, outside_nil]; decide
  · refine ⟨rfl, ?_, rfl⟩
    simp only [csW, callSt64At_mem, callSt64At_r3, callSt64At_r1]
    rw [h0]
    exact strOut_strMem [0x80] (by simp) 0x2000 (by simp)

/-- **Non-vacuity**: the toy allocator, the toy writer (`(len, nil)`), and a concrete call state (`*z = 0x011234`, 17 bits: the
multi-byte path) meet every hypothesis of `correctness`, contracts included. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (s : State),
    NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      NewobjectSite H rt 4096 s_c) ∧
    ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 7).toNat = (sc.regs 1).toNat) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 fn ∧
      ICallPre64 4 stack 56 rt
        (fun sc => sc.regs 0 = w ∧
          StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
          (sc.regs 7).toNat = (sc.regs 1).toNat) s_c) ∧
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
        H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ (∃ ptr len cap n e1 e2, R w ptr len cap n e1 e2 ∧ s'.regs 0 = e1 ∧ s'.regs 3 = e2) ∧
        (z ≠ 0 → s'.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 56 - stack, (s.regs 4).toNat + 32)]) := by
  refine ⟨impl, rt, H, A0, stack, R0, zA, tabA, wA, retA, s0, hnew, ⟨csNew, csNew_rip, csNew_pre⟩, ?w1,
    ⟨csW, rfl, csW_pre⟩, hret, setup, pre,
    correctness impl rt H A0 stack R0 zA tabA wA hnew ?w1 retA hret s0 setup pre⟩
  case w1 => exact hw zA wA

end Witness

end Fv256.Amd64.EncodeRLP
