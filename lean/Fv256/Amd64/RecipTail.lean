import Fv256.Amd64.RecipLive
import Fv256.Amd64.RecipShr
import Fv256.Amd64.RecipStage5Lem

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_tail {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xc49)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 : Nat)
    (hL : Lc49 s S xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90)
    (hc : xc49rcx < 64) (e1 : xc49m78 = xc49rbx) (e2 : xc49m80 = xc49rsi) (e3 : xc49m88 = xc49r9) (e4 : xc49m90 = xc49r11) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xd1b)) S (fun S' =>
      ∃ xd1bm240 xd1bm248 xd1bm250 xd1bm258 xd1bm260,
        Ld1b s S' xd1bm240 xd1bm248 xd1bm250 xd1bm258 xd1bm260 ∧
        xd1bm240 + 2 ^ 64 * xd1bm248 + 2 ^ 128 * xd1bm250 + 2 ^ 192 * xd1bm258 + 2 ^ 256 * xd1bm260 =
          (xc49rdx + 2 ^ 64 * xc49rbx + 2 ^ 128 * xc49rsi + 2 ^ 192 * xc49r9 + 2 ^ 256 * xc49r11) / 2 ^ xc49rcx ∧
        RecRegs s S' ∧ RecMem s S'.mem y3) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xc49rcx, hB_xc49rcx, hE_xc49rdx, hB_xc49rdx, hE_xc49rbx, hB_xc49rbx, hE_xc49rsi, hB_xc49rsi, hE_xc49r9, hB_xc49r9, hE_xc49r11, hB_xc49r11, hE_xc49m78, hB_xc49m78, hE_xc49m80, hB_xc49m80, hE_xc49m88, hB_xc49m88, hE_xc49m90, hB_xc49m90⟩ := hL
  have hcm : xc49rcx % 64 = xc49rcx := Nat.mod_eq_of_lt hc
  rcases Nat.eq_zero_or_pos xc49rcx with h0 | hpos
  · subst h0
    janus64_run [Util.readLE_32, hE_xc49rcx, hE_xc49rdx, hE_xc49rbx, hE_xc49rsi, hE_xc49r9, hE_xc49r11, hE_xc49m78, hE_xc49m80, hE_xc49m88, hE_xc49m90, hsp4, Nat.mod_eq_of_lt hB_xc49rcx, Nat.mod_eq_of_lt hB_xc49rdx, Nat.mod_eq_of_lt hB_xc49rbx, Nat.mod_eq_of_lt hB_xc49rsi, Nat.mod_eq_of_lt hB_xc49r9, Nat.mod_eq_of_lt hB_xc49r11, Nat.mod_eq_of_lt hB_xc49m78, Nat.mod_eq_of_lt hB_xc49m80, Nat.mod_eq_of_lt hB_xc49m88, Nat.mod_eq_of_lt hB_xc49m90]
    all_goals (try fv_carry_simp_v1)
    all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
    all_goals (try simp only [← BitVec.ofNat_add])
    all_goals (try fv_carry_simp_v1)
    refine ⟨xc49rdx, xc49m78, xc49m80, xc49m88, xc49m90, ?_, ?_, ?_, ?_⟩
    · unfold Ld1b
      refine ⟨?_, hB_xc49rdx, ?_, hB_xc49m78, ?_, hB_xc49m80, ?_, hB_xc49m88, ?_, hB_xc49m90⟩
      all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
        Nat.mod_eq_of_lt hB_xc49rdx, Nat.mod_eq_of_lt hB_xc49m78, Nat.mod_eq_of_lt hB_xc49m80, Nat.mod_eq_of_lt hB_xc49m88, Nat.mod_eq_of_lt hB_xc49m90]
    · rw [e1, e2, e3, e4]; simp only [Nat.pow_zero, Nat.div_one]
    · unfold RecRegs
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr4
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr5
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr14
      · exact hx
    · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
      all_goals first | exact hM | omega
  · janus64_run [Util.readLE_32, hE_xc49rcx, hE_xc49rdx, hE_xc49rbx, hE_xc49rsi, hE_xc49r9, hE_xc49r11, hE_xc49m78, hE_xc49m80, hE_xc49m88, hE_xc49m90, hsp4, Nat.mod_eq_of_lt hB_xc49rcx, Nat.mod_eq_of_lt hB_xc49rdx, Nat.mod_eq_of_lt hB_xc49rbx, Nat.mod_eq_of_lt hB_xc49rsi, Nat.mod_eq_of_lt hB_xc49r9, Nat.mod_eq_of_lt hB_xc49r11, Nat.mod_eq_of_lt hB_xc49m78, Nat.mod_eq_of_lt hB_xc49m80, Nat.mod_eq_of_lt hB_xc49m88, Nat.mod_eq_of_lt hB_xc49m90, hcm]
    all_goals (try fv_carry_simp_v1)
    all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
    all_goals (try simp only [← BitVec.ofNat_add])
    all_goals (try fv_carry_simp_v1)
    have hmsb : (BitVec.ofNat 64 xc49rcx).msb = false := by
      cases h : (BitVec.ofNat 64 xc49rcx).msb
      · rfl
      · exact absurd ((msb_iff xc49rcx (by omega)).1 h) (by omega)
    have hk : (18446744073709551616 - xc49rcx) % 64 = 64 - xc49rcx := by omega
    have hmask : 18446744073709551616 - (18446744073709551552 + xc49rcx) < 64 := by omega
    simp only [hmsb, hk, hmask, ↓reduceIte]
    try simp only [e1, e2, e3, e4]
    have t0 := tw xc49rdx xc49rbx xc49rcx hB_xc49rdx hB_xc49rbx hpos hc
    have t1 := tw' xc49rbx xc49rsi xc49rcx hB_xc49rbx hB_xc49rsi hpos hc
    have t2 := tw' xc49rsi xc49r9 xc49rcx hB_xc49rsi hB_xc49r9 hpos hc
    have t3 := tw' xc49r9 xc49r11 xc49rcx hB_xc49r9 hB_xc49r11 hpos hc
    have t4 := tw4 xc49r11 xc49rcx hB_xc49r11
    have l0 := tw_lt xc49rdx xc49rbx xc49rcx hB_xc49rdx
    have l1 := tw_lt xc49rbx xc49rsi xc49rcx hB_xc49rbx
    have l2 := tw_lt xc49rsi xc49r9 xc49rcx hB_xc49rsi
    have l3 := tw_lt xc49r9 xc49r11 xc49rcx hB_xc49r9
    have l4 : xc49r11 >>> xc49rcx < 2 ^ 64 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hB_xc49r11
    refine ⟨(xc49rdx >>> xc49rcx ||| (xc49rbx <<< (64 - xc49rcx)) % 2 ^ 64), (xc49rbx >>> xc49rcx ||| (xc49rsi <<< (64 - xc49rcx)) % 2 ^ 64), (xc49rsi >>> xc49rcx ||| (xc49r9 <<< (64 - xc49rcx)) % 2 ^ 64), (xc49r9 >>> xc49rcx ||| (xc49r11 <<< (64 - xc49rcx)) % 2 ^ 64), (xc49r11 >>> xc49rcx), ?_, ?_, ?_, ?_⟩
    · unfold Ld1b
      refine ⟨?_, l0, ?_, l1, ?_, l2, ?_, l3, ?_, l4⟩
      all_goals simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
        t0, t1, t2, t3, t4, Nat.mod_eq_of_lt l0, Nat.mod_eq_of_lt l1, Nat.mod_eq_of_lt l2, Nat.mod_eq_of_lt l3, Nat.mod_eq_of_lt l4]
    · exact shr5 xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 hpos hc hB_xc49rdx hB_xc49rbx hB_xc49rsi hB_xc49r9 hB_xc49r11
    · unfold RecRegs
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr4
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr5
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hr14
      · exact hx
    · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
      all_goals first | exact hM | omega

end Fv256.Amd64.RecipSeg
