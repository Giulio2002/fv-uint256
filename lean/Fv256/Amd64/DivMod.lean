import Fv256.Amd64.CallSites.Live
import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL
import Fv256.Amd64.UdivremM
import Fv256.Amd64.DivModB
import Fv256.Amd64.DivModW

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.DivMod

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := Extracted.dataAddr.«type:uint256.Int#33f34945»

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m]
      (fun s => StackGuardOK s 0x198 ∧ StackWritable s 4256 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4256) (4256 + 0x28) rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 true ∧
        Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16) ∧
        Outside ((s.regs 14).toNat + 16) 8 rt ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 0xa0) (rtView rt s.mem))
      (fun s s' => s'.regs 0 = z ∧
        ∃ m' : Nat, (s'.regs 3).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
          (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
          valueAt s' z 32 = Fv256.B.divSpec (valueAt s x 32) (valueAt s y 32) ∧
          s'.mem.readLE m' 32 = Fv256.B.modSpec (valueAt s x 32) (valueAt s y 32) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
            ((s.regs 4).toNat - 4256, (s.regs 4).toNat + 0x28)])) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hout, hal, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩,
    hzo, hxo, hyo, hmo, hdz, hdx, hdy, hdm, hzm, hdg, hgo, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hgo hH
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hout hal
  simp only [valueAt]
  janus64_data hd [hacc]
  have hx0 := Util.readLE8_lt s.mem x.toNat
  have hx1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have hx2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have hx3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hy0 := Util.readLE8_lt s.mem y.toNat
  have hy1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have hy2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have hy3 := Util.readLE8_lt s.mem (y.toNat + 24)
  have hdv := Nat.div_le_self (s.mem.readLE x.toNat 8) (s.mem.readLE y.toNat 8)
  have hx0' : s.xmm 15 = 0#128 := by simpa using h_x15
  janus64_run [Util.readLE_32] until [Extracted.entry + 0x8c] calls [hnew.pos]
  · -- the path with the un-aliasing allocation (z = m)
    rename_i ptr junk fl xx yh mm zh kr cfr cin clt cacc cal8 cal16 czb ctriv
    have hzm' : z = m := BitVec.eq_of_toNat_eq (by omega)
    have hdj := InRanges.disjoint cin hout
    have hdzp := InRanges.disjoint cin hzo
    have hOut : ∀ a n, (s.regs 4).toNat - 4256 ≤ a → a + n ≤ (s.regs 4).toNat + 40 → Outside a n rt :=
      fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
    have hOc : ∀ a n, (s.regs 4).toNat - 144 ≤ a → a + n ≤ (s.regs 4).toNat + 40 →
        Outside a n (rt ++ [((s.regs 4).toNat - 160 - 4096, (s.regs 4).toNat - 160),
          ((s.regs 4).toNat - 160 + 8, (s.regs 4).toNat - 160 + 8 + 8)]) := fun a n h1 h2 => by
      simp only [Janus.outside_append, Janus.outside_cons, Janus.outside_nil, and_true]
      exact ⟨hOut a n (by omega) h2, by omega, by omega⟩
    have hsp8 : mm.readLE ((s.regs 4).toNat + 8) 8 = z.toNat := by
      rw [cfr.readLE _ _ (hOc _ _ (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by simpa using z.isLt)
    have hsp16 : mm.readLE ((s.regs 4).toNat + 16) 8 = x.toNat := by
      rw [cfr.readLE _ _ (hOc _ _ (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by simpa using x.isLt)
    have hsp24 : mm.readLE ((s.regs 4).toNat + 24) 8 = y.toNat := by
      rw [cfr.readLE _ _ (hOc _ _ (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by simpa using y.isLt)
    have hsp0 : mm.readLE (s.regs 4).toNat 8 = ret := by
      rw [cfr.readLE _ _ (hOc _ _ (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact h_ret
    have hspm8 : mm.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      rw [cfr.readLE _ _ (hOc _ _ (by omega) (by omega))]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by simpa using (s.regs 5).isLt)
    refine Fv256.Amd64.DivModB.partB impl rt z x y m ptr.toNat ret hret s _ hg hlow hnw hacc hout hzw hz hxw hx hyw hy
      (by omega) cacc hxo hyo hzo (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) hgo
      ⟨fun h => absurd hzm' h, fun _ => ⟨cin, by omega, cacc⟩⟩ (Or.inl cin)
      ?hrip ?h0 ?h3 ?h1 ?h7 ?h4 ?h5 ?h14 ?hx15 ?hdf ?hsx15 ?hfr ?hspill ?hretslot ?hbp
    case hrip => exact (by decide : (4948460#64 : BitVec 64) = BitVec.ofNat 64 (Extracted.entry + 140))
    case h4 => simp [callRegs64, setRegF]; bv_omega
    case hx15 => simp [hx0']
    case hsx15 => exact hx0'
    case hdf => rfl
    case hfr => janus_frame
    all_goals (simp (disch := omega) [callRegs64, setRegF, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hsp8, hsp16, hsp24, hsp0, hspm8])
  · -- no allocation: z != m, the numbers stay where they are
    have hne : z.toNat ≠ m.toNat := by omega
    have hzm2 : z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat := by
      rcases hzm with h | h | h
      · exact absurd (congrArg BitVec.toNat h) hne
      · exact Or.inl h
      · exact Or.inr h
    have hOut : ∀ a n, (s.regs 4).toNat - 4256 ≤ a → a + n ≤ (s.regs 4).toNat + 40 → Outside a n rt :=
      fun a n h1 h2 => Outside.of_sub hout h1 (by omega)
    have hsp8 : (Arm64.Memory.writeLE (Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) ((s.regs 4).toNat + 8) 8 z.toNat).readLE ((s.regs 4).toNat + 8) 8 = z.toNat := by
      rw [Janus.Arm64.Memory.readLE_writeLE_self]
      exact Nat.mod_eq_of_lt (by simpa using z.isLt)
    have hsp0 : (Arm64.Memory.writeLE (Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) ((s.regs 4).toNat + 8) 8 z.toNat).readLE (s.regs 4).toNat 8 = ret := by
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
      exact h_ret
    have hspm8 : (Arm64.Memory.writeLE (Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat) ((s.regs 4).toNat + 8) 8 z.toNat).readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat := by
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
      exact Nat.mod_eq_of_lt (by simpa using (s.regs 5).isLt)
    refine Fv256.Amd64.DivModB.partB impl rt z x y m m.toNat ret hret s _ hg hlow hnw hacc hout hzw hz hxw hx hyw hy
      hmw hm hxo hyo hzo (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) (by unfold Apart; omega) hgo
      ⟨fun _ => rfl, fun h => absurd (by rw [h]) hne⟩ (Or.inr rfl)
      ?n_hrip ?n_h0 ?n_h3 ?n_h1 ?n_h7 ?n_h4 ?n_h5 ?n_h14 ?n_hx15 ?n_hdf ?n_hsx15 ?n_hfr ?n_hspill ?n_hretslot ?n_hbp
    case n_hrip => exact (by decide : (4948460#64 : BitVec 64) = BitVec.ofNat 64 (Extracted.entry + 140))
    case n_h0 => exact h_a0
    case n_h3 => exact h_a1
    case n_h1 => exact h_a2
    case n_h7 => exact congrArg BitVec.toNat h_a3
    case n_h4 => rfl
    case n_h5 => rfl
    case n_h14 => rfl
    case n_hx15 => exact hx0'
    case n_hdf => rfl
    case n_hsx15 => exact hx0'
    case n_hfr => janus_frame
    case n_hspill => exact hsp8
    case n_hretslot => exact hsp0
    case n_hbp => exact hspm8


namespace Witness

open Fv256.Amd64.DivModW

/-- Non-vacuity of `correctness`: every hypothesis holds together for a concrete runtime (a toy allocator at
`runtime.newobject`'s address), a concrete call of `DivMod` (distinct `z`, `x`, `y`, `m`), and the call returns. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (ret : Nat) (s : Amd64.State),
    NewobjectContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧
      (NewobjectPre64 4096 s_c ∧ Ready64 H rt [(s_c.regs 0).toNat] s_c)) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, x, y, m] s ∧
    (StackGuardOK s 0x198 ∧ StackWritable s 4256 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4256) (4256 + 0x28) rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 true ∧
        Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4256 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16) ∧
        Outside ((s.regs 14).toNat + 16) 8 rt ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 0xa0) (rtView rt s.mem)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s (fun s' => ABIReturn s s' ∧ (s'.regs 0 = z ∧
        ∃ m' : Nat, (s'.regs 3).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
          (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
          valueAt s' z 32 = Fv256.B.divSpec (valueAt s x 32) (valueAt s y 32) ∧
          s'.mem.readLE m' 32 = Fv256.B.modSpec (valueAt s x 32) (valueAt s y 32) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
            ((s.regs 4).toNat - 4256, (s.regs 4).toNat + 0x28)]))) :=
  ⟨impl, rtW, HW, zW, xW, yW, mW, retW, s0, hnewW, ⟨csNewW, csNewW_rip, csNewW_pre⟩, hretW, setupW, preW,
    correctness impl rtW HW zW xW yW mW hnewW retW hretW s0 setupW preW⟩

end Witness

end Fv256.Amd64.DivMod
