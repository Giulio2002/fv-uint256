import Fv256.Proofs.Arm64.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.UtilE64
import Fv256.Proofs.Common.DecMath
import Fv256.Proofs.Arm64.DecT
import Fv256.Proofs.Arm64.DecA
import Fv256.Proofs.Arm64.DecB
import Fv256.Proofs.Arm64.DecC
import Fv256.Proofs.Arm64.DecD

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec

set_option maxHeartbeats 8000000 in
/-- One 9-digit chunk of `formatBase10` (`2^29 ≤ u`): back to the head `fb+0x28` with `u/10^9 ≠ 0` in `R3`, or to the return block `fb+0x1ec` when `u < 10^9`. -/
theorem chunk (s : State) (tgt ptr len u i : Nat)
    (htg : (10 ^ 9 ≤ u ∧ tgt = fb + 0x28) ∨ (u < 10 ^ 9 ∧ tgt = fb + 0x1ec))
    (hu : u < 2 ^ 64) (hu29 : 2 ^ 29 ≤ u) (hi : 9 ≤ i) (hil : i ≤ len) (hp : ptr + len ≤ 2 ^ 48)
    (hacc : s.mem.accessible ptr len true = true) (hd : TabsOK s.mem)
    (hpc : s.pc = BitVec.ofNat 64 (fb + 0x28)) (e0 : s.regs 0 = BitVec.ofNat 64 ptr) (e2 : s.regs 2 = BitVec.ofNat 64 len)
    (e1 : s.regs 1 = BitVec.ofNat 64 i) (e3 : s.regs 3 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.Arm64.DecProg.program (BitVec.ofNat 64 tgt) s (fun S' =>
      S'.regs 0 = BitVec.ofNat 64 ptr ∧ S'.regs 2 = BitVec.ofNat 64 len ∧ S'.regs 1 = BitVec.ofNat 64 (i - 9) ∧
      S'.regs 4 = BitVec.ofNat 64 (u / 10 ^ 9) ∧ (u / 10 ^ 9 ≠ 0 → S'.regs 3 = BitVec.ofNat 64 (u / 10 ^ 9)) ∧
      (∀ k, k ∉ [1, 3, 4, 5, 6, 7, 8, 9, 10, 11] → S'.regs k = s.regs k) ∧ S'.sp = s.sp ∧
      (∀ k, k < 9 → S'.mem.readLE (ptr + i - 1 - k) 1 = 48 + u / 10 ^ k % 10) ∧
      MemFrame s.mem S'.mem [(ptr + i - 9, ptr + i)] ∧ TabsOK S'.mem) := by
  refine reachesRet64_bind (chunk_pre s u hu hu29 hpc e3) ?_
  rintro S1 hpc1 ⟨a3, a4, a6, ak, asp, amem⟩
  have hx0 : u % 10 ^ 9 < 10 ^ 9 := Nat.mod_lt _ (by decide)
  have hacc1 : S1.mem.accessible ptr len true = true := by rw [amem]; exact hacc
  have hd1 : TabsOK S1.mem := by rw [amem]; exact hd
  refine reachesRet64_bind (inner_loop ptr len (u % 10 ^ 9) i (by omega) hil hx0 hp 3 0 S1 (by omega) hacc1 hd1 hpc1
    (by rw [ak 0 (by simp), e0]) (by rw [ak 2 (by simp), e2]) (by rw [ak 1 (by simp), e1]; rfl)
    (by rw [a6]) (by rw [a3]; simp)) ?_
  rintro S2 hpc2 ⟨b0, b2, b1, b3, b6, bk, bsp, bm, bfr, btab⟩
  have hacc2 : S2.mem.accessible ptr len true = true := by rw [bfr.accessible]; exact hacc1
  have hlo : u % 10 ^ 9 / 10 ^ 8 < 10 := by omega
  refine reachesRet64_mono (chunk_post S2 tgt ptr len (i - 8) (u % 10 ^ 9 / 10 ^ 8) (u / 10 ^ 9)
    (by rcases htg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inr ⟨by omega, h2⟩) (by omega) (by omega) hlo (by omega) hp hacc2 btab hpc2 b0 b2
    (by rw [b1]) (by rw [b3]) (by rw [bk 4 (by simp), a4])) ?_
  rintro S3 ⟨c0, c2, c1, c4, c3, ck, csp, cm, cfr, ctab⟩
  refine ⟨c0, c2, ?_, c4, c3, ?_, ?_, ?_, ?_, ctab⟩
  · rw [c1]; congr 1
  · intro k hk
    rw [ck k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
      bk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
      ak k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
  · rw [csp, bsp, asp]
  · intro k hk
    by_cases hk8 : k = 8
    · subst hk8
      have := cm
      rw [show ptr + (i - 8) - 1 = ptr + i - 1 - 8 by omega] at this
      rw [this]
      have hdm := digit_mod u 8 9 (by omega)
      have hlt : u % 10 ^ 9 / 10 ^ 8 < 10 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hdm
      omega
    · have hout : Outside (ptr + i - 1 - k) 1 [(ptr + (i - 8) - 1, ptr + (i - 8))] := by
        simp only [Outside, and_true]; omega
      rw [cfr.readLE _ _ hout, bm k (by omega) (by omega), dig9 u k (by omega)]
  · rw [← amem]
    refine MemFrame.trans (m' := S2.mem) (rs := [(ptr + i - 9, ptr + i)]) (rs' := [(ptr + i - 9, ptr + i)]) ?_ ?_ (fun a n h => ⟨h, h⟩)
    · exact bfr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
    · exact cfr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
end Fv256.Arm64.Dec
