import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.SetBytesDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem case15 (z ptr cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, BitVec.ofNat 64 15, cap]
      (fun s => GuardOK s 48 ∧ StackOK s 88 72 ∧ Extracted.program.DataLoaded s.mem ∧ (BitVec.ofNat 64 15).toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr (BitVec.ofNat 64 15).toNat false ∧
        Disjoint z.toNat 32 (ptr.toNat + (BitVec.ofNat 64 15).toNat - used (BitVec.ofNat 64 15).toNat) (used (BitVec.ofNat 64 15).toNat) ∧
        Disjoint z.toNat 32 (s.sp.toNat - 88) 160 ∧
        Disjoint (ptr.toNat + (BitVec.ofNat 64 15).toNat - used (BitVec.ofNat 64 15).toNat) (used (BitVec.ofNat 64 15).toNat) (s.sp.toNat - 88) 160 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 88) 160)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + (BitVec.ofNat 64 15).toNat - used (BitVec.ofNat 64 15).toNat + i) 1) (used (BitVec.ofNat 64 15).toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 88) 160) := by
    intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hdg⟩
    janus_intro hs
    janus_data hd [hw]
    simp only [Disjoint] at hdg
    simp only [Disjoint, used, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, ite_true, Nat.add_sub_cancel] at hd1 hd2 hd3 hp ⊢
    janus_run
    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]⟩
         have := Util.rd1_lt s.mem (ptr.toNat); have := Util.rd1_lt s.mem (ptr.toNat + 1); have := Util.rd1_lt s.mem (ptr.toNat + 2); have := Util.rd1_lt s.mem (ptr.toNat + 3); have := Util.rd1_lt s.mem (ptr.toNat + 4); have := Util.rd1_lt s.mem (ptr.toNat + 5); have := Util.rd1_lt s.mem (ptr.toNat + 6); have := Util.rd1_lt s.mem (ptr.toNat + 7); have := Util.rd1_lt s.mem (ptr.toNat + 8); have := Util.rd1_lt s.mem (ptr.toNat + 9); have := Util.rd1_lt s.mem (ptr.toNat + 10); have := Util.rd1_lt s.mem (ptr.toNat + 11); have := Util.rd1_lt s.mem (ptr.toNat + 12); have := Util.rd1_lt s.mem (ptr.toNat + 13); have := Util.rd1_lt s.mem (ptr.toNat + 14); (try simp only [Util.chunk8, Util.chunk4, Util.chunk2, Util.chunk2n, Util.rot0]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; (try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Nat.mod_eq_of_lt]); (try omega)))

end Fv256.Arm64.SetBytes
