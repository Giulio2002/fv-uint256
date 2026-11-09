import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.PadDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.PaddedBytes

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem case19 (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hmk : MakesliceContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.makeslice") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, 19#64]
      (fun s => GuardOK s 0 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4144) 4168 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
        H [byteType, 19, 19] (s.regs 28).toNat (s.sp.toNat - 48) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ (s'.regs 1).toNat = 19 ∧ (s'.regs 2).toNat = 19 ∧
        InRanges ptr 19 rt ∧ s'.mem.accessible ptr 19 true = true ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + i) 1) 19 = val256 s.mem z.toNat % 2 ^ (8 * 19) ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4144, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : byteType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x30] calls [hmk.pos]
  rename_i wobj wregs wflags wvreg wmem wo wx hmf hin hle hacc h8 h16 hzb htr
  have hdj := InRanges.disjoint hin hout
  have hdz := InRanges.disjoint hin hzo
  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.sub_self, BitVec.zero_add, BitVec.add_sub_cancel, Util.bv_add_sub_left]
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨_, rfl, hin.sub (Nat.le_refl _) (by omega), Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega), ?_, ?_⟩
  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)
    intro a ha
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; omega) | omega
  · janus_frame

end Fv256.Arm64.PaddedBytes
