import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2
import Fv256.UtilH
import Fv256.Arm64.DivMod

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts
open Fv256.Arm64.DivMod

namespace Fv256.Arm64.DivModMain

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z x y m : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, x, y, m]
      (fun s => GuardOK s 464 ∧ StackOK s 4256 40 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4256) (4256 + 40) rt ∧
        Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Ptr32 s.mem y false ∧ Ptr32 s.mem m true ∧
        Outside z.toNat 32 rt ∧ Outside x.toNat 32 rt ∧ Outside y.toNat 32 rt ∧ Outside m.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint x.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
        Disjoint y.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧ Disjoint m.toNat 32 (s.sp.toNat - 4256) (4256 + 40) ∧
        (z = m ∨ Disjoint32 z.toNat m.toNat) ∧
        ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 4256 ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
        Outside ((s.regs 28).toNat + 16) 8 rt ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 160) (rtView rt s.mem))
      (fun s s' => s'.regs 0 = z ∧
        ∃ m' : Nat, (s'.regs 1).toNat = m' ∧ (z ≠ m → m' = m.toNat) ∧
          (z = m → InRanges m' 32 rt ∧ m' % 16 = 0 ∧ s'.mem.accessible m' 32 true = true) ∧
          val256 s'.mem z.toNat = Fv256.B.divSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          val256 s'.mem m' = Fv256.B.modSpec (val256 s.mem x.toNat) (val256 s.mem y.toNat) ∧
          MemFrame s.mem s'.mem (rt ++ [(z.toNat, z.toNat + 32), (m.toNat, m.toNat + 32),
            (s.sp.toNat - 4256, s.sp.toNat + 40)])) := by
  intro ret hret s hs ⟨hg, ⟨hal, hb, ha, hw⟩, hd, hout, hzp, hxp, hyp, hmp, hzo, hxo, hyo, hmo, hdz, hdx, hdy, hdm, hzm, hdg, hgo, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  obtain ⟨⟨hzb, hza⟩, ⟨hxb, hxa⟩, ⟨hyb, hya⟩, ⟨hmb, hma⟩⟩ := And.intro hzp (And.intro hxp (And.intro hyp hmp))
  simp only [Disjoint] at hdz hdx hdy hdm
  obtain ⟨hg1, hg2, hg3⟩ := hg
  janus_run until [Extracted.entry + 0x64] calls [hnew.pos]
  all_goals trace_state
  all_goals sorry

end Fv256.Arm64.DivModMain
