import Extracted
import Fv256.Spec
import Fv256.Util

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToSlice

set_option maxHeartbeats 64000000 in
theorem caseBig (z d len cap : BitVec 64) (h32 : 32 ≤ len.toNat) (hlen : len.toNat < 2 ^ 48) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (fun s => StackWritable s 8 24 ∧ Buffer s z 32 false ∧ Buffer s d 32 true ∧
        (z.toNat + 32 ≤ d.toNat ∨ d.toNat + 32 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (d.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat))
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) 32 = valueAt s z 32 % 2 ^ (8 * 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat 32 ((s.regs regSP).toNat - 8) 32) := by
  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hdw, hd⟩, hzd, hzs, hds⟩
  janus64_intro hs
  simp only [regSP] at hacc hlow hnw hzs hds
  simp only [valueAt, Disjoint]
  have e1 : (len - 1#64).toNat = len.toNat - 1 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := len.isLt; omega
  have hmin : (if 31 < ((len.toNat - 1 : Nat) : Int) then 31#64 else len - 1#64) = 31#64 := by
    split
    · rfl
    · apply BitVec.eq_of_toNat_eq
      rw [e1]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x1a]
  rw [hmin]
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] until [Extracted.entry + 0x7c]
  all_goals try clear hbr
  janus64_run [Util.readLE_32, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod] (budget := 4000000)
  all_goals try clear hbr
  have l0 := Util.readLE8_lt s.mem z.toNat
  have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
  refine ⟨?_, ?_⟩
  · exact Util.chain32d _ d.toNat _ _ _ _ l0 l1 l2 l3
  · refine Util.chain32d_ow2 _ _ _ _ _ _ _ _ _ l0 l1 l2 l3 ?_
    simp (disch := omega) only [Util.ow2_wr_iff, Util.ow2_self_iff]

end Fv256.Amd64.WriteToSlice
