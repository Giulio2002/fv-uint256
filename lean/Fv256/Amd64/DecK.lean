import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.Amd64.DecE
import Fv256.Amd64.DecG
import Fv256.Amd64.DecH
import Fv256.Amd64.DecI
import Fv256.Amd64.DecJ

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- A frame inside the buffer keeps the 16 stack bytes at `sp`. -/
theorem stack_pres {M M' : Memory} {a b ptr len sp : Nat} (hf : MemFrame M M' [(a, b)])
    (h1 : ptr ≤ a) (h2 : b ≤ ptr + len) (hdisj : ptr + len ≤ sp ∨ sp + 16 ≤ ptr)
    (hs : M.accessible sp 16 true = true) :
    M'.accessible sp 16 true = true ∧ M'.readLE sp 8 = M.readLE sp 8 ∧ M'.readLE (sp + 8) 8 = M.readLE (sp + 8) 8 := by
  refine ⟨by rw [hf.accessible]; exact hs, ?_, ?_⟩
  · exact hf.readLE _ _ (by simp only [Outside, and_true]; omega)
  · exact hf.readLE _ _ (by simp only [Outside, and_true]; omega)

theorem dig_shift (u0 c k : Nat) : u0 / 10 ^ c / 10 ^ k % 10 = u0 / 10 ^ (c + k) % 10 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

set_option maxHeartbeats 16000000 in
theorem outer (s0 : State) (ptr len u0 i0 sp bp ret : Nat) (hu0 : u0 < 2 ^ 64) (hdl : decLen u0 ≤ i0)
    (hil : i0 ≤ len) (hp : ptr + len ≤ 2 ^ 48) (hsp : sp + 16 ≤ 2 ^ 48) (hdisj : ptr + len ≤ sp ∨ sp + 16 ≤ ptr)
    (hret : ret < 2 ^ 47) :
    ∀ u c (R : Nat → W64) (fl : Flags) (M : Memory), u = u0 / 10 ^ c → c + decLen u ≤ i0 →
      M.accessible ptr len true = true → Extracted.program.DataLoaded M →
      M.accessible sp 16 true = true → M.readLE sp 8 = bp → M.readLE (sp + 8) 8 = ret →
      R 0 = BitVec.ofNat 64 ptr → R 3 = BitVec.ofNat 64 (i0 - c) → R 1 = BitVec.ofNat 64 len →
      R 7 = BitVec.ofNat 64 u → R 4 = BitVec.ofNat 64 sp →
      (∀ k, k < c → M.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) → (0 < u ∨ c = 0) →
      ReachesRet Extracted.program (BitVec.ofNat 64 ret)
        { s0 with regs := R, rip := BitVec.ofNat 64 (fb + 0x17), flags := fl, mem := M }
        (fun S' => ∃ (R' : Nat → W64) (fl' : Flags) (M' : Memory),
          S' = { s0 with regs := R', rip := BitVec.ofNat 64 ret, flags := fl', mem := M' } ∧
          R' 0 = BitVec.ofNat 64 (i0 - decLen u0) ∧ R' 4 = BitVec.ofNat 64 (sp + 16) ∧ R' 5 = BitVec.ofNat 64 bp ∧
          (∀ k, k ∉ [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] → R' k = R k) ∧
          (∀ k, k < decLen u0 → M'.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10) ∧
          MemFrame M M' [(ptr + i0 - decLen u0, ptr + i0 - c)] ∧ Extracted.program.DataLoaded M') := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro c R fl M hu hdc hacc hd hsa hm0 hm1 e0 e3 e1 e7 e4 hw hpos
    have hu64 : u < 2 ^ 64 := by
      rw [hu]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hu0
    have hlt : u < 10 ^ decLen u := decLen_lt_pow u
    by_cases hbig : 10 ^ 9 ≤ u
    · have hdl9 : decLen u = decLen (u / 10 ^ 9) + 9 := decLen_div_pow u 9 hbig
      have hc0 : decLen u0 = decLen u + c := by
        by_cases hc : c = 0
        · subst hc; simp [hu]
        · have : 0 < u := by omega
          have h1 : 10 ^ c ≤ u0 := by
            rw [hu] at this
            exact (Nat.le_div_iff_mul_le (Nat.one_le_pow c 10 (by omega))).1 this |> fun h => by omega
          rw [decLen_div_pow u0 c h1, ← hu]
      refine Fv256.E.reachesRet_bind (chunk_loop s0 ptr len u (i0 - c) R fl M hu64 hbig (by omega) (by omega) hp hacc hd
        e0 e3 e1 e7) ?_
      rintro S ⟨R1, fl1, M1, rfl, a0, a3, a1, a7, ak, am, afr, ad⟩
      obtain ⟨hs1, hm01, hm11⟩ := stack_pres afr (by omega) (by omega) hdisj hsa
      have hacc1 : M1.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
      have hw1 : ∀ k, k < c + 9 → M1.readLE (ptr + i0 - 1 - k) 1 = 48 + u0 / 10 ^ k % 10 := by
        intro k hk
        by_cases hkc : k < c
        · have hout : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - 9, ptr + (i0 - c))] := by
            simp only [Outside, and_true]; omega
          rw [afr.readLE _ _ hout, hw k hkc]
        · have := am (k - c) (by omega)
          rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega, hu, dig_shift] at this
          rw [this, show c + (k - c) = k by omega]
      have hu' : u / 10 ^ 9 = u0 / 10 ^ (c + 9) := by
        rw [hu, Nat.div_div_eq_div_mul, ← Nat.pow_add]
      refine ReachesRet.mono (ih (u / 10 ^ 9) (Nat.div_lt_self (by omega) (by decide)) (c + 9) R1 fl1 M1 hu' (by omega) hacc1 ad hs1
        (by rw [hm01, hm0]) (by rw [hm11, hm1]) a0 (by rw [a3]; congr 1) a1 a7 (by rw [ak 4 (by simp), e4]) hw1
        (Or.inl (by omega))) ?_
      rintro S ⟨R2, fl2, M2, rfl, b0, b4, b5, bk, bm, bfr, bd⟩
      refine ⟨R2, fl2, M2, rfl, b0, b4, b5, ?_, bm, ?_, bd⟩
      · intro k hk
        rw [bk k hk, ak k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
      · refine afr.trans bfr ?_
        intro a n h
        simp only [Outside, and_true] at h ⊢
        omega
    · by_cases hmid : 2 ^ 29 ≤ u
      · have hdl9 : decLen u = 9 := decLen_of u 9 (by omega) (by
          have : 10 ^ (9 - 1) ≤ 2 ^ 29 := by decide
          omega) (by omega)
        have hc0 : decLen u0 = decLen u + c := by
          by_cases hc : c = 0
          · subst hc; simp [hu]
          · have : 0 < u := by omega
            have h1 : 10 ^ c ≤ u0 := by
              rw [hu] at this
              exact (Nat.le_div_iff_mul_le (Nat.one_le_pow c 10 (by omega))).1 this |> fun h => by omega
            rw [decLen_div_pow u0 c h1, ← hu]
        refine Fv256.E.reachesRet_bind (chunk_ret s0 ptr len u (i0 - c) R fl M hu64 (by omega) hmid (by omega) (by omega) hp hacc hd
          e0 e3 e1 e7) ?_
        rintro S ⟨R1, fl1, M1, rfl, a0, a1, a7, ak, am, afr, ad⟩
        obtain ⟨hs1, hm01, hm11⟩ := stack_pres afr (by omega) (by omega) hdisj hsa
        have hacc1 : M1.accessible ptr len true = true := by rw [afr.accessible]; exact hacc
        have hret' := tail1b4 s0 sp bp ret R1 fl1 M1 hsp (Janus.Arm64.Memory.accessible_sub M1 hs1 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _))
          (by rw [ak 4 (by simp), e4]) (by rw [hm01, hm0]) (by rw [hm11, hm1]) hret
        refine ReachesRet.mono hret' ?_
        rintro S ⟨R2, fl2, rfl, b4, b5, bk⟩
        refine ⟨R2, fl2, M1, rfl, ?_, b4, b5, ?_, ?_, ?_, ad⟩
        · rw [bk 0 (by simp), a0, hc0, hdl9]; congr 1; omega
        · intro k hk
          rw [bk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
            ak k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
        · intro k hk
          rw [hc0, hdl9] at hk
          by_cases hkc : k < c
          · have hout : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - 9, ptr + (i0 - c))] := by
              simp only [Outside, and_true]; omega
            rw [afr.readLE _ _ hout, hw k hkc]
          · have := am (k - c) (by omega)
            rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega, hu, dig_shift] at this
            rw [this, show c + (k - c) = k by omega]
        · exact afr.mono (fun a n h => by simp only [Outside, and_true] at h ⊢; omega)
      · have hu29 : u < 2 ^ 29 := by omega
        have hc0 : decLen u0 = decLen u + c := by
          by_cases hc : c = 0
          · subst hc; simp [hu]
          · have : 0 < u := by omega
            have h1 : 10 ^ c ≤ u0 := by
              rw [hu] at this
              exact (Nat.le_div_iff_mul_le (Nat.one_le_pow c 10 (by omega))).1 this |> fun h => by omega
            rw [decLen_div_pow u0 c h1, ← hu]
        have hdu : decLen u ≤ i0 - c := by omega
        refine Fv256.E.reachesRet_bind (to_final s0 u R fl M hu29 e7) ?_
        rintro S ⟨R1, fl1, rfl, a2, ak⟩
        refine Fv256.E.reachesRet_bind (fin_loop s0 ptr len u (i0 - c) hu29 hdu (by omega) hp u 0 R1 fl1 M (by simp)
          (by simpa using hdu) hacc hd (by rw [ak 0 (by simp), e0]) (by rw [ak 3 (by simp), e3]; rfl)
          (by rw [ak 1 (by simp), e1]) a2 (by intro k hk; omega)) ?_
        rintro S ⟨R2, fl2, M2, c', rfl, hc1, hz, hdc', hlt100, b0, b1, b3, b2, bk, bm, bfr, bd⟩
        obtain ⟨hs2, hm02, hm12⟩ := stack_pres bfr (by omega) (by omega) hdisj hsa
        have hacc2 : M2.accessible ptr len true = true := by rw [bfr.accessible]; exact hacc
        have hc'0 : decLen u = c' + decLen (u / 10 ^ c') := by
          rcases hz with h | h
          · rw [h]; simp
          · have h1 : 10 ^ c' ≤ u := (Nat.le_div_iff_mul_le (Nat.one_le_pow c' 10 (by omega))).1 h |> fun h => by omega
            have := decLen_div_pow u c' h1
            omega
        refine Fv256.E.reachesRet_bind (fin_last s0 ptr len (u / 10 ^ c') (i0 - c - c') R2 fl2 M2 hlt100 (by omega) (by omega) hp hacc2
          b0 b3 b1 b2 bd) ?_
        rintro S ⟨R3, fl3, M3, rfl, d6, dk, dm, dfr, dd⟩
        obtain ⟨hs3, hm03, hm13⟩ := stack_pres dfr (by omega) (by omega) hdisj hs2
        have hret' := tail199 s0 sp bp ret R3 fl3 M3 hsp (Janus.Arm64.Memory.accessible_sub M3 hs3 (Or.inl rfl) (Nat.le_refl _) (Nat.le_refl _))
          (by rw [dk 4 (by simp), bk 4 (by simp), ak 4 (by simp), e4])
          (by rw [hm03, hm02, hm0]) (by rw [hm13, hm12, hm1]) hret
        refine ReachesRet.mono hret' ?_
        rintro S ⟨R4, fl4, rfl, f0, f4, f5, fk⟩
        refine ⟨R4, fl4, M3, rfl, ?_, f4, f5, ?_, ?_, ?_, dd⟩
        · rw [f0, d6, hc0]; congr 1; omega
        · intro k hk
          have hk' : k ∉ [0, 4, 5] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega
          rw [fk k hk', dk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
            bk k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega),
            ak k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢; omega)]
        · intro k hk
          rw [hc0] at hk
          by_cases hkc : k < c
          · have hout1 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c) - c', ptr + (i0 - c))] := by
              simp only [Outside, and_true]; omega
            have hout2 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c - c') - decLen (u / 10 ^ c'), ptr + (i0 - c - c'))] := by
              simp only [Outside, and_true]; omega
            rw [dfr.readLE _ _ hout2, bfr.readLE _ _ hout1, hw k hkc]
          · by_cases hk2 : k - c < c'
            · have hout2 : Outside (ptr + i0 - 1 - k) 1 [(ptr + (i0 - c - c') - decLen (u / 10 ^ c'), ptr + (i0 - c - c'))] := by
                simp only [Outside, and_true]; omega
              have := bm (k - c) hk2
              rw [show ptr + (i0 - c) - 1 - (k - c) = ptr + i0 - 1 - k by omega, hu, dig_shift] at this
              rw [dfr.readLE _ _ hout2, this, show c + (k - c) = k by omega]
            · have := dm (k - c - c') (by omega)
              rw [show ptr + (i0 - c - c') - 1 - (k - c - c') = ptr + i0 - 1 - k by omega, hu, dig_shift, dig_shift,
                show c + (c' + (k - c - c')) = k by omega] at this
              rw [this]
        · refine bfr.trans dfr (rs'' := [(ptr + i0 - decLen u0, ptr + i0 - c)]) ?_
          intro a n h
          simp only [Outside, and_true] at h ⊢
          omega
end Fv256.Amd64.Dec
