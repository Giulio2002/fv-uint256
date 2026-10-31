import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC64
import Fv256.Amd64.FromBigSfb

/-!
# `uint256.FromBig(b *big.Int) (*Int, bool)` (amd64)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts

namespace Fv256.Amd64.FromBig

def intType : Nat := dataBase Extracted.program 0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Buffer s x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Buffer s pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          (x.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ x.toNat) ∧
          (pw.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ pw.toNat)))
      (fun s s' => (x.toNat = 0 → s'.regs 0 = 0 ∧ s'.regs 3 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          s'.mem.readLE ptr 32 =
            Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          (s'.regs 3).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)]))) := by
  intro ret hret s hs ⟨hg, ⟨hb, ha, hw⟩, hd, hout, hal, hH, hxx⟩
  janus64_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hb ha hw hout hal hxx ⊢
  janus64_data hd [hw]
  janus64_run until [Extracted.entry + 0x25] calls [hnew.pos]
  · exact fun h => h.elim
  · obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hx9⟩ := hxx hbr
    obtain ⟨hxw, hxa⟩ := hx1
    obtain ⟨hpw, hpa⟩ := hx5
    have hdx := InRanges.disjoint ‹InRanges _ 32 rt› hx6
    have hdp := InRanges.disjoint ‹InRanges _ 32 rt› hx7
    have hds := InRanges.disjoint ‹InRanges _ 32 rt› hout
    janus64_run calls [Fv256.Amd64.FromBigSfb.sfb_summary impl _ x pw len]
    rename_i wa wb wc wd we wf wg wh hfr hin hle hacc h8 h16 hz rr a cpc csp c28 c29 c30 c18 cfs cfr cflag cval
    refine ⟨fun h => h.elim, _, rfl, hin, h16, hacc, ?_, cflag, ?_⟩
    · rw [Util.readLE_32]
      rw [Fv256.C.bigAbs_write, Fv256.C.bigAbs_write, Fv256.C.bigAbs_frame _ _ _ _ _ hfr, Fv256.C.bigAbs_write,
        Fv256.C.bigAbs_write, Fv256.C.bigAbs_write] at cval
      · exact cval
      all_goals first
        | omega
        | (simp only [outside_append, outside_cons, outside_nil, and_true]
           exact ⟨hx7, by omega, by omega⟩)
    · janus_frame

end Fv256.Amd64.FromBig
