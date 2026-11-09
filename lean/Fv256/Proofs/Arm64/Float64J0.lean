import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.UtilD

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option maxHeartbeats 4000000 in
theorem lem0 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => (Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0) ∧ ((s.mem.readLE (x.toNat + 8) 8) = 0 ∧ (s.mem.readLE (x.toNat + 16) 8) = 0 ∧ (s.mem.readLE (x.toNat + 24) 8) = 0))
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩, ⟨h1, h2, h3⟩⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  have hor : (s.mem.readLE (x.toNat + 8) 8 ||| s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 24) 8 = 0) := by
    simp [h1, h2, h3]
  janus_run [hf, hor, h1, h2, h3]
  all_goals clear_states
  all_goals (simp only [State.getV, setVReg_apply, ite_true, BitVec.toNat_ofNat] at *)
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  have hlt : Janus.Float.fromInt Janus.Float.binary64 .rne (s.mem.readLE x.toNat 8) < 2 ^ 64 :=
    Janus.Float.fromInt_lt Janus.Float.binary64 .rne _
  have hx0 := Util.readLE8_lt s.mem x.toNat
  rw [FP.fixedToFP_ieee FP.IEEEMode.zero, show FP.roundingMode 0 = .rne from rfl]
  simp only [Bool.true_or, ite_true]
  unfold Fv256.B.float64BitsNearest
  simp only [h1, h2, h3, val256, Nat.mul_zero, Nat.add_zero] at *
  simp only [Nat.reducePow] at hlt hx0 ⊢
  omega

end Fv256.Arm64.Float64
