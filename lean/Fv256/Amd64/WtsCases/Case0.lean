import Extracted
import Fv256.Spec
import Fv256.Util

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.WriteToSlice

set_option maxHeartbeats 64000000 in
theorem case0 (z d cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, 0#64, cap]
      (fun s => StackWritable s 8 24 ∧ Buffer s z 32 false ∧ Buffer s d 0 true ∧
        (z.toNat + 32 ≤ d.toNat ∨ d.toNat + 0 ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (d.toNat + 0 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24 ≤ d.toNat) ∧ 0 ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) 0 = valueAt s z 32 % 2 ^ (8 * 0) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat 0 ((s.regs regSP).toNat - 8) 32) := by
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
  · simp [Spec.fromBE, Nat.mod_one]
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

end Fv256.Amd64.WriteToSlice
