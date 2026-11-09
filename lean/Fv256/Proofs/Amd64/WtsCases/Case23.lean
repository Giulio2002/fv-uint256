import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToSlice

set_option maxHeartbeats 64000000 in
theorem case23 (z d cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, 23#64, cap]
      (fun s => StackWritable s 8 24 ∧ Buffer s z 32 false ∧ Buffer s d 23 true ∧
        (z.toNat + 32 ≤ d.toNat ∨ d.toNat + 23 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (d.toNat + 23 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat) ∧ 23 ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) 23 = valueAt s z 32 % 2 ^ (8 * 23) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat 23 ((s.regs regSP).toNat - 8) 32) := by
  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hdw, hd⟩, hzd, hzs, hds, hcap⟩
  janus64_intro hs
  simp only [regSP] at hacc hlow hnw hzs hds
  simp only [valueAt, Disjoint]
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod]
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨?_, ?_⟩
  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)
    intro a ha
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 22 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb176 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb176 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb168 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb168 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb160 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb160 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb152 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb152 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb144 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb136 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb128 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb120 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb112 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb104 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb96 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb88 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb80 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb72 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb64 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb56 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb48 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb40 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb32 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb24 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      simp (disch := omega) only [Util.rb8_mem_byte, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reducePow, Nat.reduceMul, Util.add_sub_norm, Nat.reduceSub, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      first | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; omega) | omega
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

end Fv256.Amd64.WriteToSlice
