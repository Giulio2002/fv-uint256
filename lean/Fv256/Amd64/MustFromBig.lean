import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC64
import Fv256.Amd64.MustFromBigSfb

/-!
# `uint256.MustFromBig(b *big.Int) *Int` (amd64)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.PanicAmd64

namespace Fv256.Amd64.MustFromBig

def intType : Nat := dataBase Extracted.program 0
def panicType : Nat := dataBase Extracted.program 1
def panicData : Nat := dataBase Extracted.program 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem correctness (P : PanicRuntime) (impl : List Janus.Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (x pw len : BitVec 64)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4136 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4136) 4160 rt ∧ (s.regs 4).toNat % 8 = 0 ∧
        H [intType] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt s.mem) ∧
        (x.toNat ≠ 0 → Buffer s x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
          s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
          Buffer s pw (8 * len.toNat) false ∧ Outside x.toNat 32 rt ∧ Outside pw.toNat (8 * len.toNat) rt ∧
          (x.toNat + 32 ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ x.toNat) ∧
          (pw.toNat + 8 * len.toNat ≤ (s.regs 4).toNat - 4136 ∨ (s.regs 4).toNat + 24 ≤ pw.toNat)))
      (fun _ => goClass P)
      (fun s s' => (x.toNat = 0 ∨ len.toNat ≤ 4) ∧
        (x.toNat = 0 → s'.regs 0 = 0) ∧
        (x.toNat ≠ 0 → ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧
          s'.mem.accessible ptr 32 true = true ∧
          s'.mem.readLE ptr 32 =
            Fv256.C.fromBig (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4136, (s.regs 4).toNat + 24)])))
      (fun s v _ => x.toNat ≠ 0 ∧ 4 < len.toNat ∧ v = ⟨panicType, panicData⟩) := by
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
  refine GoReturns.of_reaches ?_
  janus64_run until [Extracted.entry + 0x2d] calls [hnew.pos]
  all_goals (trace_state; fail "x")

end Fv256.Amd64.MustFromBig
