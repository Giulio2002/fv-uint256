import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.CodeIn
import Fv256.ChainProg
import Fv256.ModProg
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL
import Fv256.Amd64.ModSum
import Fv256.Amd64.AddModShapes

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.AddModFast

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcMod : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ModProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
set_option profiler true in
set_option profiler.threshold 5000 in
theorem fast (z x y m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, m]
      (fun s => (fun s => StackGuardOK s 0x300 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x348 0x28 ∧ Extracted.program.DataLoaded s.mem ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ y.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ m.toNat) ∧
        (z = m ∨ z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        (z = y ∨ z.toNat + 32 ≤ y.toNat ∨ y.toNat + 32 ≤ z.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x348 ∨ (s.regs regSP).toNat + 0x28 ≤ (s.regs regG).toNat + 16) ∧
        ((s.regs regG).toNat + 24 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs regG).toNat + 16)) s ∧ (s.mem.readLE (m.toNat + 24) 8 ≠ 0 ∧ s.mem.readLE (x.toNat + 24) 8 ≤ s.mem.readLE (m.toNat + 24) 8 ∧ s.mem.readLE (y.toNat + 24) 8 ≤ s.mem.readLE (m.toNat + 24) 8))
      (fun s s' => s'.regs 0 = z ∧ s'.mem.readLE z.toNat 32 = Fv256.F.addmodSpec (s.mem.readLE x.toNat 32) (s.mem.readLE y.toNat 32) (s.mem.readLE m.toNat 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x348, (s.regs regSP).toNat + 0x28)]) := by
  intro ret hret s hs ⟨⟨hg, hsp, ⟨hlow, hnw, hacc⟩, hdata, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdm, hzm, hzx, hzy, hdg, hdgz⟩, hcase⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdgz
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdm hsp
  janus64_data hdata [hacc]
  obtain ⟨hm3, hx3, hy3⟩ := hcase
  janus64_run [Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero5, Fv256.F.wv_zero5', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.xor_ofNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div]
  all_goals (refine ⟨?_, ?_⟩)
  all_goals (first | janus_frame | skip)
  all_goals (first
    | (with_reducible apply Fv256.F.shape0 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape1 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape2 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape3 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape4 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape5 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape6 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape7 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape8 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape9 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape10 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption))
    | (with_reducible apply Fv256.F.shape11 <;> first | with_reducible exact Util.readLE8_lt _ _ | (with_reducible assumption)))

end Fv256.Amd64.AddModFast
