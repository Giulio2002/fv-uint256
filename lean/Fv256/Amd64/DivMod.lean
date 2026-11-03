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

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.DivMod

/-- The address of `uint256.Int`'s type descriptor (the `LEA` before the call loads it): the extraction's only data object. -/
def intType : Nat := dataBase Extracted.program 0

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m]
      (fun s => StackGuardOK s 0x190 ∧ StackWritable s 4248 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4248) (4248 + 0x28) rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 true ∧
        Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4248 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16) ∧
        Outside ((s.regs 14).toNat + 16) 8 rt ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 0x98) (rtView rt s.mem))
      (fun s s' => s'.regs 0 = z ∧
        ∃ m' : Nat, (s'.regs 3).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
          (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
          valueAt s' z 32 = Fv256.B.divSpec (valueAt s x 32) (valueAt s y 32) ∧
          s'.mem.readLE m' 32 = Fv256.B.modSpec (valueAt s x 32) (valueAt s y 32) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
            ((s.regs 4).toNat - 4248, (s.regs 4).toNat + 0x28)])) := by
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
  janus64_run [Util.readLE_32] until [Extracted.entry + 0x8c] calls [hnew.pos]
  all_goals (first
    | (have hdj := InRanges.disjoint ‹InRanges _ 32 rt› hout
       have hdz' := InRanges.disjoint ‹InRanges _ 32 rt› hzo
       have hdx' := InRanges.disjoint ‹InRanges _ 32 rt› hxo
       have hdy' := InRanges.disjoint ‹InRanges _ 32 rt› hyo
       have hdgo := InRanges.disjoint ‹InRanges _ 32 rt› hgo
       refine Fv256.Amd64.DivModB.partB impl rt z x y m _ ret hret s _ hg hlow hnw hacc hout hzw hz hxw hx hyw hy ?_ ?_ hxo hyo hzo hdz hdx hdy ?_ ?_ hdg hgo ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h_x15 ?_ ?_ ?_ ?_
       all_goals trace_state
       all_goals sorry)
    | skip)
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.DivMod
