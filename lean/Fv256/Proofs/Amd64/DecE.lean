import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Amd64.DecA
import Fv256.Proofs.Amd64.DecB
import Fv256.Proofs.Amd64.DecC
import Fv256.Proofs.Amd64.DecD

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Dec

theorem dig9 (u k : Nat) (hk : k < 9) : u % 1000000000 / 10 ^ k % 10 = u / 10 ^ k % 10 := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] <;> omega

set_option maxHeartbeats 8000000 in
/-- One 9-digit chunk of `formatBase10` when more digits remain (`u / 10^9 ≠ 0`): back at the loop head `fb+0x17`. -/
theorem chunk_loop (s0 : State) (ptr len u i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hu : u < 2 ^ 64) (hu9 : 10 ^ 9 ≤ u) (hi : 9 ≤ i) (hil : i ≤ len) (hp : ptr + len ≤ 2 ^ 48)
    (hacc : M.accessible ptr len true = true) (hd : TabsOK M)
    (e0 : R 0 = BitVec.ofNat 64 ptr) (e3 : R 3 = BitVec.ofNat 64 i) (e1 : R 1 = BitVec.ofNat 64 len)
    (e7 : R 7 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.DecProg.program (BitVec.ofNat 64 (fb + 0x17))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x17), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x17), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 ptr ∧ R' 3 = BitVec.ofNat 64 (i - 9) ∧ R' 1 = BitVec.ofNat 64 len ∧
        R' 7 = BitVec.ofNat 64 (u / 10 ^ 9) ∧ (∀ k, k ∉ [0, 2, 3, 6, 7, 8, 9, 10, 11] → R' k = R k) ∧
        (∀ k, k < 9 → M'.readLE (ptr + i - 1 - k) 1 = 48 + u / 10 ^ k % 10) ∧
        MemFrame M M' [(ptr + i - 9, ptr + i)] ∧ TabsOK M') := by
  have hu29 : 2 ^ 29 ≤ u := by
    have : 2 ^ 29 ≤ 10 ^ 9 := by decide
    omega
  refine Fv256.E.reachesRet_bind (chunk_pre s0 u R fl M hu hu29 (by rw [e7])) ?_
  rintro S ⟨R1, fl1, rfl, a0, a3, a1, a7, a6, a2, ak⟩
  have hx0 : u % 10 ^ 9 < 10 ^ 9 := Nat.mod_lt _ (by decide)
  refine Fv256.E.reachesRet_bind (inner_loop s0 ptr len (u % 10 ^ 9) i (by omega) hil hx0 hp 4 0 R1 fl1 M (by omega) hacc hd
    (by rw [a0]) (by rw [a3, e3]; rfl) (by rw [a1, e1]) (by rw [a7, e0]) (by rw [a6]; simp)) ?_
  rintro S ⟨R2, fl2, M2, rfl, b0, b3, b6, bk, bm, bfr, bd⟩
  have hacc2 : M2.accessible ptr len true = true := by rw [bfr.accessible]; exact hacc
  have hlo : u % 10 ^ 9 / 10 ^ 8 < 10 := by omega
  have hud : u / 10 ^ 9 ≠ 0 := by omega
  have hud2 : u / 10 ^ 9 < 2 ^ 64 := by omega
  refine ReachesRet.mono (chunk_post_loop s0 ptr len (i - 8) (u % 10 ^ 9 / 10 ^ 8) (u / 10 ^ 9) R2 fl2 M2 (by omega) (by omega) hlo hud hud2
    hp hacc2 bd (by rw [bk 1 (by simp), a1, e1]) b3 b6 (by rw [bk 2 (by simp), a2]) (by rw [bk 7 (by simp), a7, e0])) ?_
  rintro S ⟨R3, fl3, M3, rfl, c0, c3, c7, c1, ck, cm, cfr, cd⟩
  refine ⟨R3, fl3, M3, rfl, c0, ?_, ?_, c7, ?_, ?_, ?_, cd⟩
  · rw [c3]; congr 1
  · rw [c1, bk 1 (by simp), a1, e1]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    rw [ck k (by simp [List.mem_cons]; omega), bk k (by simp [List.mem_cons]; omega), ak k (by simp [List.mem_cons]; omega)]
  · intro k hk
    by_cases hk8 : k = 8
    · subst hk8
      have := cm
      rw [show ptr + (i - 8) - 1 = ptr + i - 1 - 8 by omega] at this
      rw [this]; omega
    · have hout : Outside (ptr + i - 1 - k) 1 [(ptr + (i - 8) - 1, ptr + (i - 8))] := by
        simp only [Outside, and_true]; omega
      rw [cfr.readLE _ _ hout, bm k (by omega) (by omega), dig9 u k (by omega)]
  · refine bfr.trans cfr ?_
    intro a n h
    simp only [Outside, and_true] at h ⊢
    omega
set_option maxHeartbeats 8000000 in
/-- One 9-digit chunk of `formatBase10` when no digits remain (`u < 10^9`): at the return block `fb+0x1b4`. -/
theorem chunk_ret (s0 : State) (ptr len u i : Nat) (R : Nat → W64) (fl : Flags) (M : Memory)
    (hu : u < 2 ^ 64) (hu9 : u < 10 ^ 9) (hu29 : 2 ^ 29 ≤ u) (hi : 9 ≤ i) (hil : i ≤ len) (hp : ptr + len ≤ 2 ^ 48)
    (hacc : M.accessible ptr len true = true) (hd : TabsOK M)
    (e0 : R 0 = BitVec.ofNat 64 ptr) (e3 : R 3 = BitVec.ofNat 64 i) (e1 : R 1 = BitVec.ofNat 64 len)
    (e7 : R 7 = BitVec.ofNat 64 u) :
    ReachesRet Fv256.DecProg.program (BitVec.ofNat 64 (fb + 0x1b4))
      { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x17), flags := fl, mem := M }
      (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
        S' = { s0 with regs := R', rip := BitVec.ofNat 64 (fb + 0x1b4), flags := fl', mem := M' } ∧
        R' 0 = BitVec.ofNat 64 (i - 9) ∧ R' 1 = BitVec.ofNat 64 len ∧ R' 7 = BitVec.ofNat 64 ptr ∧ (∀ k, k ∉ [0, 2, 3, 6, 7, 8, 9, 10, 11] → R' k = R k) ∧
        (∀ k, k < 9 → M'.readLE (ptr + i - 1 - k) 1 = 48 + u / 10 ^ k % 10) ∧
        MemFrame M M' [(ptr + i - 9, ptr + i)] ∧ TabsOK M') := by
  refine Fv256.E.reachesRet_bind (chunk_pre s0 u R fl M hu hu29 (by rw [e7])) ?_
  rintro S ⟨R1, fl1, rfl, a0, a3, a1, a7, a6, a2, ak⟩
  have hx0 : u % 10 ^ 9 < 10 ^ 9 := Nat.mod_lt _ (by decide)
  refine Fv256.E.reachesRet_bind (inner_loop s0 ptr len (u % 10 ^ 9) i (by omega) hil hx0 hp 4 0 R1 fl1 M (by omega) hacc hd
    (by rw [a0]) (by rw [a3, e3]; rfl) (by rw [a1, e1]) (by rw [a7, e0]) (by rw [a6]; simp)) ?_
  rintro S ⟨R2, fl2, M2, rfl, b0, b3, b6, bk, bm, bfr, bd⟩
  have hacc2 : M2.accessible ptr len true = true := by rw [bfr.accessible]; exact hacc
  have hlo : u % 10 ^ 9 / 10 ^ 8 < 10 := by omega
  have hud : u / 10 ^ 9 = 0 := by omega
  refine ReachesRet.mono (chunk_post_ret s0 ptr len (i - 8) (u % 10 ^ 9 / 10 ^ 8) (u / 10 ^ 9) R2 fl2 M2 (by omega) (by omega) hlo hud
    hp hacc2 bd (by rw [bk 1 (by simp), a1, e1]) b3 b6 (by rw [bk 2 (by simp), a2, hud]) (by rw [bk 7 (by simp), a7, e0])) ?_
  rintro S ⟨R3, fl3, M3, rfl, c0, c3, c7, c1, ck, cm, cfr, cd⟩
  refine ⟨R3, fl3, M3, rfl, ?_, ?_, c7, ?_, ?_, ?_, cd⟩
  · rw [c0]; congr 1
  · rw [c1, bk 1 (by simp), a1, e1]
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    rw [ck k (by simp [List.mem_cons]; omega), bk k (by simp [List.mem_cons]; omega), ak k (by simp [List.mem_cons]; omega)]
  · intro k hk
    by_cases hk8 : k = 8
    · subst hk8
      have := cm
      rw [show ptr + (i - 8) - 1 = ptr + i - 1 - 8 by omega] at this
      rw [this]; omega
    · have hout : Outside (ptr + i - 1 - k) 1 [(ptr + (i - 8) - 1, ptr + (i - 8))] := by
        simp only [Outside, and_true]; omega
      rw [cfr.readLE _ _ hout, bm k (by omega) (by omega), dig9 u k (by omega)]
  · refine bfr.trans cfr ?_
    intro a n h
    simp only [Outside, and_true] at h ⊢
    omega

end Fv256.Amd64.Dec
