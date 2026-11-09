import Fv256.Proofs.Common.ChainProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecB
import Fv256.Proofs.Common.UtilB
import Fv256.Proofs.Common.KnuthMathB
import Fv256.Proofs.Common.UdivMathB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.UdivremA

abbrev ku : Nat := segAddr Fv256.ChainProg.program "github.com/holiman/uint256.udivrem"

theorem ku_lt : ku + 0x440 < 2 ^ 47 := by decide

-- the search for the most significant non-zero word of `d` (head at +0x34, exit at +0x4c)
set_option maxHeartbeats 8000000 in
theorem dlen_loop (s0 : State) (dp : Nat) (M : Memory)
    (hdp : dp + 32 ≤ 2 ^ 48) (hda : M.accessible dp 32 false = true) :
    ∀ t (R : Nat → W64) (fl : Flags), t ≤ 4 → R 9 = BitVec.ofNat 64 dp → R 2 = BitVec.ofNat 64 t - 1 →
      (∀ j, t ≤ j → j < 4 → M.readLE (dp + 8 * j) 8 = 0) →
      ReachesRet Fv256.ChainProg.program (BitVec.ofNat 64 (ku + 0x4c))
        { s0 with regs := R, rip := BitVec.ofNat 64 (ku + 0x34), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (n : Nat),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 (ku + 0x4c), flags := fl', mem := M } ∧
          R' 2 = BitVec.ofNat 64 n ∧ n ≤ t ∧ (∀ j, n ≤ j → j < 4 → M.readLE (dp + 8 * j) 8 = 0) ∧
          (0 < n → M.readLE (dp + 8 * (n - 1)) 8 ≠ 0) ∧ (∀ k, k ∉ [2, 12] → R' k = R k)) := by
  intro t
  induction t with
  | zero =>
    intro R fl ht r9 r2 hz
    have hcode := ku_lt
    have hneg : (R 2).msb = true := by rw [r2]; decide
    janus64_run [hneg]
    refine ⟨_, _, 0, rfl, by simp [setRegF], Nat.le_refl _, hz, fun h => absurd h (by omega), ?_⟩
    intro k hk
    have : k ≠ 2 := fun h => hk (by simp [h])
    simp [setRegF, this]
  | succ t ih =>
    intro R fl ht r9 r2 hz
    have hcode := ku_lt
    have hnn : (R 2).msb = false := by
      rw [r2, BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; simp; omega
    have hRt : R 2 = BitVec.ofNat 64 t := by rw [r2]; bv_omega
    have hxt : (R 2).toNat = t := by rw [hRt, BitVec.toNat_ofNat]; omega
    by_cases hzero : M.readLE (dp + 8 * t) 8 = 0
    · have hzero' : M.readLE (dp + t * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hzero
      janus64_run [hnn, hzero', hxt, r9] until [ku + 0x34]
      refine Fv256.B.reachesRet_mono64 (ih _ _ (by omega) (by simp [setRegF, r9]) (by simp [setRegF, hRt])
        (fun j hj1 hj2 => by
          by_cases hjt : j = t
          · subst hjt; exact hzero
          · exact hz j (by omega) hj2)) ?_
      rintro S ⟨R', fl', n, hS, h2, hn, hzz, hnz, hk⟩
      refine ⟨R', fl', n, hS, h2, by omega, hzz, hnz, ?_⟩
      intro k hk'
      rw [hk k hk']
      have h1 : k ≠ 2 := fun h => hk' (by simp [h])
      have h12 : k ≠ 12 := fun h => hk' (by simp [h])
      simp [setRegF, h1, h12]
    · have hzero' : ¬ M.readLE (dp + t * 8) 8 = 0 := by rw [Nat.mul_comm]; exact hzero
      janus64_run [hnn, hzero', hxt, r9]
      refine ⟨_, _, t + 1, rfl, ?_, Nat.le_refl _, fun j hj1 hj2 => hz j (by omega) hj2, fun _ => by simpa using hzero, ?_⟩
      · simp [setRegF, hRt]; bv_omega
      · intro k hk'
        have h1 : k ≠ 2 := fun h => hk' (by simp [h])
        have h12 : k ≠ 12 := fun h => hk' (by simp [h])
        simp [setRegF, h1, h12]

end Fv256.Amd64.UdivremA
