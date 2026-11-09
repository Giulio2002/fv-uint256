import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToSlice

set_option maxHeartbeats 64000000 in
theorem case3 (z d cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, 3#64, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧
        Ptr s.mem d 3 true ∧ Disjoint z.toNat 32 d.toNat 3 ∧
        Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat 3 (s.sp.toNat - 24) 48 ∧ 3 ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) 3 = val256 s.mem z.toNat % 2 ^ (8 * 3) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat 3 (s.sp.toNat - 24) 48) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hd, hd'⟩, hzd, hzs, hds, hcap⟩
  janus_intro hs
  simp only [Disjoint] at *
  janus_run [Util.readLE8_mod, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨?_, ?_⟩
  · refine (Util.fromBE_congr ?_).trans (Util.fromBE_bytes _ _)
    intro a ha
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb16 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb8 _ _ _ _ l0 l1 l2 l3]; omega) | omega
    · (try simp only [Nat.add_zero])
      (try simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Util.rc8_mem_byte, Janus.Arm64.Memory.readLE_writeLE_self, Nat.add_sub_cancel_left, Nat.add_sub_add_left, Nat.sub_self, Nat.reduceSub, Nat.reducePow, Nat.reduceMul])
      first | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; done) | (rw [Util.wb0 _ _ _ _ l0 l1 l2 l3]; omega) | omega
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

end Fv256.Arm64.WriteToSlice
