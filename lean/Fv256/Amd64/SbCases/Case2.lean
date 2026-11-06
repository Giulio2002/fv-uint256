import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.SetBytesDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem case2 (z ptr cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, BitVec.ofNat 64 2, cap]
      (fun s => StackGuardOK s 48 ∧ StackWritable s 88 24 ∧ Extracted.program.DataLoaded s.mem ∧ (BitVec.ofNat 64 2).toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Buffer s z 32 true ∧ Buffer s ptr (BitVec.ofNat 64 2).toNat false ∧
        (z.toNat + 32 ≤ ptr.toNat + (BitVec.ofNat 64 2).toNat - used (BitVec.ofNat 64 2).toNat ∨ ptr.toNat + (BitVec.ofNat 64 2).toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (ptr.toNat + (BitVec.ofNat 64 2).toNat ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat + (BitVec.ofNat 64 2).toNat - used (BitVec.ofNat 64 2).toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + (BitVec.ofNat 64 2).toNat - used (BitVec.ofNat 64 2).toNat + i) 1) (used (BitVec.ofNat 64 2).toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 88) 112) := by
    intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hlc, hc48, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3, hdg⟩
    janus64_intro hs
    have hgl := hg.load
    have hgb := hg.below
    have hnw2 := hg.noWrap
    have hgr := hg.readable
    simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd2 hd3 hdg
    janus64_data hd [hacc]
    simp only [valueAt]
    have hu : used (BitVec.ofNat 64 2).toNat = 2 := by simp [used]
    rw [hu] at hd1 hd3 ⊢
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_sub_cancel] at hd1 hd2 hd3 hp
    janus64_run [Util.readLE_32]
    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
         have := Util.rd1_lt s.mem (ptr.toNat); have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd2_lt s.mem (ptr.toNat); have h2b0 : s.mem.readLE (ptr.toNat) 2 = s.mem.readLE (ptr.toNat) 1 + 256 * s.mem.readLE (ptr.toNat + 1) 1 := Util.rd2_bytes s.mem (ptr.toNat); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega)))

end Fv256.Amd64.SetBytes
