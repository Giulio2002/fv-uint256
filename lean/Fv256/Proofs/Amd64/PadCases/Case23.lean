import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.PadDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem case23 (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, 23#64]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        Buffer s z 32 false ∧ Outside z.toNat 32 rt ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        H [byteType, 23, 23] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 3).toNat = 23 ∧ (s'.regs 1).toNat = 23 ∧
        InRanges ptr 23 rt ∧ s'.mem.accessible ptr 23 true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) 23 = valueAt s z 32 % 2 ^ (8 * 23) ∧
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
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 22 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb176 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb176 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb168 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb168 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb160 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb160 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb152 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb152 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Util.add_sub_norm, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rb8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; omega) | omega
  · janus_frame

end Fv256.Amd64.PaddedBytes
