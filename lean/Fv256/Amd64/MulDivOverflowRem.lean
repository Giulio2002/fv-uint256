import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.SpecF
import Fv256.UtilF
import Fv256.Amd64.UmulSum
import Fv256.CodeIn
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremK
import Fv256.Amd64.UdivremL

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulDivOverflowRem

set_option maxRecDepth 100000 in
theorem hcChain : Janus.Contracts.EqHashModel.CodeIn64 Fv256.ChainProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem hcUmul : Janus.Contracts.EqHashModel.CodeIn64 Fv256.UmulProg.program Extracted.program :=
  Fv256.CodeIn.codeIn64_of_sub _ _ (by decide) (by decide) (by decide)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem correctness (z x y d m : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x, y, d, m]
      (fun s => StackGuardOK s 0x2a8 ∧ 0x300 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x218 0x30 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s d 32 false ∧ Buffer s m 32 true ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ y.toNat) ∧
        (d.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ d.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ m.toNat) ∧
        (z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧ (x.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ y.toNat) ∧ (d.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ d.toNat) ∧
        m.toNat ≠ 0 ∧ (m.toNat + 32 ≤ (s.regs regG).toNat + 16 ∨ (s.regs regG).toNat + 24 ≤ m.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ s'.regs 3 = m ∧ valueAt s' m 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) ∧
        (s'.regs 1).toNat % 256 = (if Fv256.F.muldivOv (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) then 1 else 0) ∧
        valueAt s' z 32 = Fv256.F.muldivSpec (valueAt s x 32) (valueAt s y 32) (valueAt s d 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32), ((s.regs regSP).toNat - 0x218, (s.regs regSP).toNat + 0x30)]) := by
  intro ret hret s hs ⟨hg, hsp, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hyw, hy⟩, ⟨hdw, hd⟩, ⟨hmw, hm⟩, hdz, hdx, hdy, hdd, hdm, hzm, hxm, hym, hdmm, hm0, hdmg, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg hdmg
  simp only [regSP] at hacc hlow hnw hdz hdx hdy hdd hdm hdmg hsp
  simp only [valueAt]
  have hL : 4 ≤ 8 ∧ 8 ≤ 8 := by omega
  have hm0e : (m.toNat = 0) = False := eq_false hm0
  janus64_run [hm0e, Util.readLE_32, Fv256.B.wv_writeLE_outside, Fv256.B.wv_zero2, Fv256.B.wv_zero2', Fv256.F.wv_zero4, Fv256.F.wv_zero4', Fv256.B.wv4_eq, false_implies, BitVec.toNat_ofNat, Nat.zero_mod, Fv256.B.borrow_zero_iff, Fv256.B.or_toNat_zero_iff, Fv256.B.ofNat64_toNat_zero_iff, Fv256.B.bv128_zero_toNat, Nat.zero_div] calls [Fv256.CodeIn.lib_summary hcUmul Fv256.Amd64.UmulSum.umul_summary, Fv256.CodeIn.lib_summary hcChain (Fv256.Amd64.UdivremL.udivrem_rem_L (L := 8) (by omega))]
  all_goals (first
    | (refine ⟨?_, ?_, ?_, ?_⟩
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · simp_all [Fv256.F.muldivOv, Fv256.F.muldivSpec, Fv256.F.mulmodSpec]
       · janus_frame)
    | skip)
  have x0 := Util.readLE8_lt s.mem x.toNat
  have x1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have x2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have x3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have y0 := Util.readLE8_lt s.mem y.toNat
  have y1 := Util.readLE8_lt s.mem (y.toNat + 8)
  have y2 := Util.readLE8_lt s.mem (y.toNat + 16)
  have y3 := Util.readLE8_lt s.mem (y.toNat + 24)
  have d0 := Util.readLE8_lt s.mem d.toNat
  have d1 := Util.readLE8_lt s.mem (d.toNat + 8)
  have d2 := Util.readLE8_lt s.mem (d.toNat + 16)
  have d3 := Util.readLE8_lt s.mem (d.toNat + 24)
  rename_i hmulv hmfU W4 W3 W2 W1 W0 hq hrm hfr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrm, hmulv]
    simp only [Fv256.F.mulmodSpec]
    split
    · exfalso; omega
    · rfl
  · refine (Fv256.F.mdo_main _ _ _ (BitVec.toNat (s.regs 4)) W1 (by omega) ?_ ?_ ?_ ?_).1
    · omega
    · omega
    · omega
    · rw [hq, hmulv]
  · refine (Fv256.F.mdo_main _ _ _ (BitVec.toNat (s.regs 4)) W1 (by omega) ?_ ?_ ?_ ?_).2
    · omega
    · omega
    · omega
    · rw [hq, hmulv]
  · janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)
def m : BitVec 64 := BitVec.ofNat 64 (DST + 0x80)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 1 then x else if i = 7 then x else if i = 6 then m
      else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, x, x, m] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl, rfl⟩

theorem hpre : (StackGuardOK s0 0x2a8 ∧ 0x300 ≤ (s0.regs regSP).toNat ∧ StackWritable s0 0x218 0x30 ∧
        Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧ Buffer s0 x 32 false ∧ Buffer s0 m 32 true ∧
        (z.toNat + 32 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ x.toNat) ∧
        (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ x.toNat) ∧
        (x.toNat + 32 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ x.toNat) ∧
        (m.toNat + 32 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ m.toNat) ∧
        (z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧ (x.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ x.toNat) ∧
        (x.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ x.toNat) ∧ (x.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ x.toNat) ∧
        m.toNat ≠ 0 ∧ (m.toNat + 32 ≤ (s0.regs regG).toNat + 16 ∨ (s0.regs regG).toNat + 24 ≤ m.toNat) ∧
        ((s0.regs regG).toNat + 24 ≤ (s0.regs regSP).toNat - 0x218 ∨ (s0.regs regSP).toNat + 0x30 ≤ (s0.regs regG).toNat + 16)) := by
  refine ⟨⟨by decide, by decide, by decide⟩, by unfold regSP; decide, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | (unfold regSP regG; decide) | (unfold regSP; decide) | decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x y d m : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x, y, d, m] s ∧
    (StackGuardOK s 0x2a8 ∧ 0x300 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x218 0x30 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s d 32 false ∧ Buffer s m 32 true ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ y.toNat) ∧
        (d.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ d.toNat) ∧
        (m.toNat + 32 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ m.toNat) ∧
        (z.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ z.toNat) ∧ (x.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ x.toNat) ∧
        (y.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ y.toNat) ∧ (d.toNat + 32 ≤ m.toNat ∨ m.toNat + 32 ≤ d.toNat) ∧
        m.toNat ≠ 0 ∧ (m.toNat + 32 ≤ (s.regs regG).toNat + 16 ∨ (s.regs regG).toNat + 24 ≤ m.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - 0x218 ∨ (s.regs regSP).toNat + 0x30 ≤ (s.regs regG).toNat + 16)) :=
  ⟨ret, s0, z, x, x, x, m, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ s'.regs 3 = m ∧ (s'.regs 1).toNat % 256 = 0 ∧ valueAt s' z 32 = 0 ∧ valueAt s' m 32 = 0 := by
  refine (correctness z x x x m ret hret s0 setup hpre).mono ?_
  intro s' h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · rw [h5]
    simp only [valueAt, Fv256.F.muldivOv]
    decide
  · rw [h6]
    simp only [valueAt, Fv256.F.muldivSpec]
    decide
  · rw [h4]
    simp only [valueAt, Fv256.F.mulmodSpec]
    decide

end Witness

end Fv256.Amd64.MulDivOverflowRem
