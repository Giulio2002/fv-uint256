import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.PadDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem case2 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, 2#64]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, 2, 2] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 2 ∧ (s'.regs 1).toNat = 2 ∧
        InRanges ptr 2 rt ∧ s'.mem.accessible ptr 2 true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) 2 = valueAt s z 32 % 2 ^ (8 * 2) ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, ⟨hzw, hz⟩, hzo, hzd, hH⟩
  janus64_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hzd ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x2b] calls [hmk.pos]
  have hdj := InRanges.disjoint ‹InRanges _ _ rt› hout
  have hdz := InRanges.disjoint ‹InRanges _ _ rt› hzo
  janus64_run [Util.readLE_32, Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, Util.bv_add_sub_left, Util.bv_sub_sub_cancel]
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · exact (‹InRanges _ _ rt›).sub (Nat.le_refl _) (by omega)
  · exact Janus.Arm64.Memory.accessible_mono _ ‹Janus.Arm64.Memory.accessible _ _ _ true = true› (Nat.le_refl _) (by omega)
  · simp only [valueAt, Util.readLE_32]
    refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)
    intro a ha
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; omega) | omega
  · janus_frame

end Fv256.Amd64.PaddedBytes
