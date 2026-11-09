import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.SetBytesDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem case21 (z ptr cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, BitVec.ofNat 64 21, cap]
      (fun s => StackGuardOK s 48 ∧ StackWritable s 88 24 ∧ Extracted.program.DataLoaded s.mem ∧ (BitVec.ofNat 64 21).toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Buffer s z 32 true ∧ Buffer s ptr (BitVec.ofNat 64 21).toNat false ∧
        (z.toNat + 32 ≤ ptr.toNat + (BitVec.ofNat 64 21).toNat - used (BitVec.ofNat 64 21).toNat ∨ ptr.toNat + (BitVec.ofNat 64 21).toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ z.toNat) ∧
        (ptr.toNat + (BitVec.ofNat 64 21).toNat ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ ptr.toNat + (BitVec.ofNat 64 21).toNat - used (BitVec.ofNat 64 21).toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - 88 ∨ (s.regs regSP).toNat + 24 ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + (BitVec.ofNat 64 21).toNat - used (BitVec.ofNat 64 21).toNat + i) 1) (used (BitVec.ofNat 64 21).toNat) ∧
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
    have hu : used (BitVec.ofNat 64 21).toNat = 21 := by simp [used]
    rw [hu] at hd1 hd3 ⊢
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_sub_cancel] at hd1 hd2 hd3 hp
    janus64_run [Util.readLE_32]
    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
         have := Util.rd1_lt s.mem (ptr.toNat); have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd1_lt s.mem (ptr.toNat + 2); have := Util.rd1_lt s.mem (ptr.toNat + 3); have := Util.rd1_lt s.mem (ptr.toNat + 4); have := Util.rd1_lt s.mem (ptr.toNat + 5); have := Util.rd1_lt s.mem (ptr.toNat + 6); have := Util.rd1_lt s.mem (ptr.toNat + 7); have := Util.rd1_lt s.mem (ptr.toNat + 8); have := Util.rd1_lt s.mem (ptr.toNat + 9); have := Util.rd1_lt s.mem (ptr.toNat + 10); have := Util.rd1_lt s.mem (ptr.toNat + 11); have := Util.rd1_lt s.mem (ptr.toNat + 12); have := Util.rd1_lt s.mem (ptr.toNat + 13); have := Util.rd1_lt s.mem (ptr.toNat + 14); have := Util.rd1_lt s.mem (ptr.toNat + 15); have := Util.rd1_lt s.mem (ptr.toNat + 16); have := Util.rd1_lt s.mem (ptr.toNat + 17); have := Util.rd1_lt s.mem (ptr.toNat + 18); have := Util.rd1_lt s.mem (ptr.toNat + 19); have := Util.rd1_lt s.mem (ptr.toNat + 20); have := Util.rd2_lt s.mem (ptr.toNat); have := Util.rd2_lt s.mem (ptr.toNat + 1); have := Util.rd2_lt s.mem (ptr.toNat + 2); have := Util.rd2_lt s.mem (ptr.toNat + 3); have := Util.rd2_lt s.mem (ptr.toNat + 4); have := Util.rd2_lt s.mem (ptr.toNat + 5); have := Util.rd2_lt s.mem (ptr.toNat + 6); have := Util.rd2_lt s.mem (ptr.toNat + 7); have := Util.rd2_lt s.mem (ptr.toNat + 8); have := Util.rd2_lt s.mem (ptr.toNat + 9); have := Util.rd2_lt s.mem (ptr.toNat + 10); have := Util.rd2_lt s.mem (ptr.toNat + 11); have := Util.rd2_lt s.mem (ptr.toNat + 12); have := Util.rd2_lt s.mem (ptr.toNat + 13); have := Util.rd2_lt s.mem (ptr.toNat + 14); have := Util.rd2_lt s.mem (ptr.toNat + 15); have := Util.rd2_lt s.mem (ptr.toNat + 16); have := Util.rd2_lt s.mem (ptr.toNat + 17); have := Util.rd2_lt s.mem (ptr.toNat + 18); have := Util.rd2_lt s.mem (ptr.toNat + 19); have h2b0 : s.mem.readLE (ptr.toNat) 2 = s.mem.readLE (ptr.toNat) 1 + 256 * s.mem.readLE (ptr.toNat + 1) 1 := Util.rd2_bytes s.mem (ptr.toNat); have h2b1 : s.mem.readLE (ptr.toNat + 1) 2 = s.mem.readLE (ptr.toNat + 1) 1 + 256 * s.mem.readLE (ptr.toNat + 2) 1 := Util.rd2_bytes s.mem (ptr.toNat + 1); have h2b2 : s.mem.readLE (ptr.toNat + 2) 2 = s.mem.readLE (ptr.toNat + 2) 1 + 256 * s.mem.readLE (ptr.toNat + 3) 1 := Util.rd2_bytes s.mem (ptr.toNat + 2); have h2b3 : s.mem.readLE (ptr.toNat + 3) 2 = s.mem.readLE (ptr.toNat + 3) 1 + 256 * s.mem.readLE (ptr.toNat + 4) 1 := Util.rd2_bytes s.mem (ptr.toNat + 3); have h2b4 : s.mem.readLE (ptr.toNat + 4) 2 = s.mem.readLE (ptr.toNat + 4) 1 + 256 * s.mem.readLE (ptr.toNat + 5) 1 := Util.rd2_bytes s.mem (ptr.toNat + 4); have h2b5 : s.mem.readLE (ptr.toNat + 5) 2 = s.mem.readLE (ptr.toNat + 5) 1 + 256 * s.mem.readLE (ptr.toNat + 6) 1 := Util.rd2_bytes s.mem (ptr.toNat + 5); have h2b6 : s.mem.readLE (ptr.toNat + 6) 2 = s.mem.readLE (ptr.toNat + 6) 1 + 256 * s.mem.readLE (ptr.toNat + 7) 1 := Util.rd2_bytes s.mem (ptr.toNat + 6); have h2b7 : s.mem.readLE (ptr.toNat + 7) 2 = s.mem.readLE (ptr.toNat + 7) 1 + 256 * s.mem.readLE (ptr.toNat + 8) 1 := Util.rd2_bytes s.mem (ptr.toNat + 7); have h2b8 : s.mem.readLE (ptr.toNat + 8) 2 = s.mem.readLE (ptr.toNat + 8) 1 + 256 * s.mem.readLE (ptr.toNat + 9) 1 := Util.rd2_bytes s.mem (ptr.toNat + 8); have h2b9 : s.mem.readLE (ptr.toNat + 9) 2 = s.mem.readLE (ptr.toNat + 9) 1 + 256 * s.mem.readLE (ptr.toNat + 10) 1 := Util.rd2_bytes s.mem (ptr.toNat + 9); have h2b10 : s.mem.readLE (ptr.toNat + 10) 2 = s.mem.readLE (ptr.toNat + 10) 1 + 256 * s.mem.readLE (ptr.toNat + 11) 1 := Util.rd2_bytes s.mem (ptr.toNat + 10); have h2b11 : s.mem.readLE (ptr.toNat + 11) 2 = s.mem.readLE (ptr.toNat + 11) 1 + 256 * s.mem.readLE (ptr.toNat + 12) 1 := Util.rd2_bytes s.mem (ptr.toNat + 11); have h2b12 : s.mem.readLE (ptr.toNat + 12) 2 = s.mem.readLE (ptr.toNat + 12) 1 + 256 * s.mem.readLE (ptr.toNat + 13) 1 := Util.rd2_bytes s.mem (ptr.toNat + 12); have h2b13 : s.mem.readLE (ptr.toNat + 13) 2 = s.mem.readLE (ptr.toNat + 13) 1 + 256 * s.mem.readLE (ptr.toNat + 14) 1 := Util.rd2_bytes s.mem (ptr.toNat + 13); have h2b14 : s.mem.readLE (ptr.toNat + 14) 2 = s.mem.readLE (ptr.toNat + 14) 1 + 256 * s.mem.readLE (ptr.toNat + 15) 1 := Util.rd2_bytes s.mem (ptr.toNat + 14); have h2b15 : s.mem.readLE (ptr.toNat + 15) 2 = s.mem.readLE (ptr.toNat + 15) 1 + 256 * s.mem.readLE (ptr.toNat + 16) 1 := Util.rd2_bytes s.mem (ptr.toNat + 15); have h2b16 : s.mem.readLE (ptr.toNat + 16) 2 = s.mem.readLE (ptr.toNat + 16) 1 + 256 * s.mem.readLE (ptr.toNat + 17) 1 := Util.rd2_bytes s.mem (ptr.toNat + 16); have h2b17 : s.mem.readLE (ptr.toNat + 17) 2 = s.mem.readLE (ptr.toNat + 17) 1 + 256 * s.mem.readLE (ptr.toNat + 18) 1 := Util.rd2_bytes s.mem (ptr.toNat + 17); have h2b18 : s.mem.readLE (ptr.toNat + 18) 2 = s.mem.readLE (ptr.toNat + 18) 1 + 256 * s.mem.readLE (ptr.toNat + 19) 1 := Util.rd2_bytes s.mem (ptr.toNat + 18); have h2b19 : s.mem.readLE (ptr.toNat + 19) 2 = s.mem.readLE (ptr.toNat + 19) 1 + 256 * s.mem.readLE (ptr.toNat + 20) 1 := Util.rd2_bytes s.mem (ptr.toNat + 19); (try simp only [Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega)))

end Fv256.Amd64.SetBytes
