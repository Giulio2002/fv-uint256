import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulDivOverflow

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x y d : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d]
      (fun s => StackGuardOK s 0x2a8 ∧ 0x300 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x218 0x28 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s d 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
        (d.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ d.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ True) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hdw, hd⟩, hdz, hdx, hdy, hdd, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdd hsp
  simp only [valueAt]
  have hL : 4 ≤ 8 ∧ 8 ≤ 8 := by omega
  janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero4, Fv256.F.wv_zero4', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.Amd64.UdivremL.udivrem_nil_L (L := 8) (by omega)]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.MulDivOverflow
