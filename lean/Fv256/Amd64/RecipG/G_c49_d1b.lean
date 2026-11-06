import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_c49_d1b (s : State) (y3 : Nat) (xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 : Nat) (S' : State) : Prop :=
  ∃ xd1bm240 xd1bm248 xd1bm250 xd1bm258 xd1bm260, Ld1b s S' xd1bm240 xd1bm248 xd1bm250 xd1bm258 xd1bm260 ∧ xd1bm240 = ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then BitVec.ofNat 64 xc49rdx ||| BitVec.ofNat 64 xc49rbx &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64 else BitVec.ofNat 64 xc49rdx).toNat) % 18446744073709551616 ∧ xd1bm248 = ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49rsi &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49rbx else BitVec.ofNat 64 xc49m78).toNat) % 18446744073709551616 ∧ xd1bm250 = ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49r9 &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49rsi else BitVec.ofNat 64 xc49m80).toNat) % 18446744073709551616 ∧ xd1bm258 = ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49r11 &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49m88 else BitVec.ofNat 64 xc49m88).toNat) % 18446744073709551616 ∧ xd1bm260 = ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then BitVec.ofNat 64 xc49r11 else BitVec.ofNat 64 xc49m90).toNat) % 18446744073709551616 ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_c49_d1b {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xc49)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90 : Nat) (hL : Lc49 s S xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0xd1b)) S (P_c49_d1b s y3 xc49rcx xc49rdx xc49rbx xc49rsi xc49r9 xc49r11 xc49m78 xc49m80 xc49m88 xc49m90) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_xc49rcx, hB_xc49rcx, hE_xc49rdx, hB_xc49rdx, hE_xc49rbx, hB_xc49rbx, hE_xc49rsi, hB_xc49rsi, hE_xc49r9, hB_xc49r9, hE_xc49r11, hB_xc49r11, hE_xc49m78, hB_xc49m78, hE_xc49m80, hB_xc49m80, hE_xc49m88, hB_xc49m88, hE_xc49m90, hB_xc49m90⟩ := hL
  janus64_run [Util.readLE_32, hE_xc49rcx, hE_xc49rdx, hE_xc49rbx, hE_xc49rsi, hE_xc49r9, hE_xc49r11, hE_xc49m78, hE_xc49m80, hE_xc49m88, hE_xc49m90, hsp4, Nat.mod_eq_of_lt hB_xc49rcx, Nat.mod_eq_of_lt hB_xc49rdx, Nat.mod_eq_of_lt hB_xc49rbx, Nat.mod_eq_of_lt hB_xc49rsi, Nat.mod_eq_of_lt hB_xc49r9, Nat.mod_eq_of_lt hB_xc49r11, Nat.mod_eq_of_lt hB_xc49m78, Nat.mod_eq_of_lt hB_xc49m80, Nat.mod_eq_of_lt hB_xc49m88, Nat.mod_eq_of_lt hB_xc49m90]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_c49_d1b
  refine ⟨((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then BitVec.ofNat 64 xc49rdx ||| BitVec.ofNat 64 xc49rbx &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64 else BitVec.ofNat 64 xc49rdx).toNat) % 18446744073709551616, ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49rsi &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49rbx else BitVec.ofNat 64 xc49m78).toNat) % 18446744073709551616, ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49r9 &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49rsi else BitVec.ofNat 64 xc49m80).toNat) % 18446744073709551616, ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then (BitVec.ofNat 64 xc49r11 &&& if (18446744073709551616 - (xc49rcx - 64)) % 18446744073709551616 < 64 then 18446744073709551615#64 else 0#64) ||| BitVec.ofNat 64 xc49m88 else BitVec.ofNat 64 xc49m88).toNat) % 18446744073709551616, ((if ¬xc49rcx = 0 ∧ (BitVec.ofNat 64 xc49rcx).msb = false then BitVec.ofNat 64 xc49r11 else BitVec.ofNat 64 xc49m90).toNat) % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Ld1b
    and_intros
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold RecRegs
    and_intros
    · simp [setRegF, hr4]
    · simp [setRegF, hr5]
    · simp [setRegF, hr14]
    · simp [hx]
  · repeat (refine RecMem.write ?_ _ _ _ hlow ?_ ?_ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.RecipSeg
