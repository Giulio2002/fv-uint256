import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

def P_14c_160 (s : State) (y3 : Nat) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat) (S' : State) : Prop :=
  ∃ x160rax x160rcx, L160 s S' x160rax x160rcx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 ∧ x160rax = (if x14crdx = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x14crax).toNat ∧ x160rcx = (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x14crcx) &&& 63#32) - 1#64).toNat ∧ RecRegs s S' ∧ RecMem s S'.mem y3

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_14c_160 {y3 : Nat} (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0x14c)) (hs : RecPre s)
    (hR : RecRegs s S) (hM : RecMem s S.mem y3) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat) (hL : L14c s S x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x160)) S (P_14c_160 s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨hr4, hr5, hr14, hx⟩ := hR
  have hfr := hM.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x14crax, hB_x14crax, hE_x14crcx, hB_x14crcx, hE_x14crdx, hB_x14crdx, hE_x14crbx, hB_x14crbx, hE_x14crsi, hB_x14crsi, hE_x14crdi, hB_x14crdi, hE_x14cr8, hB_x14cr8, hE_x14cr9, hB_x14cr9, hE_x14cm208, hB_x14cm208, hE_x14cm210, hB_x14cm210, hE_x14cm218, hB_x14cm218, hE_x14cm220, hB_x14cm220⟩ := hL
  janus64_run [Util.readLE_32, hE_x14crax, hE_x14crcx, hE_x14crdx, hE_x14crbx, hE_x14crsi, hE_x14crdi, hE_x14cr8, hE_x14cr9, hE_x14cm208, hE_x14cm210, hE_x14cm218, hE_x14cm220, hsp4, Nat.mod_eq_of_lt hB_x14crax, Nat.mod_eq_of_lt hB_x14crcx, Nat.mod_eq_of_lt hB_x14crdx, Nat.mod_eq_of_lt hB_x14crbx, Nat.mod_eq_of_lt hB_x14crsi, Nat.mod_eq_of_lt hB_x14crdi, Nat.mod_eq_of_lt hB_x14cr8, Nat.mod_eq_of_lt hB_x14cr9, Nat.mod_eq_of_lt hB_x14cm208, Nat.mod_eq_of_lt hB_x14cm210, Nat.mod_eq_of_lt hB_x14cm218, Nat.mod_eq_of_lt hB_x14cm220]
  all_goals (try fv_carry_simp_v1)
  all_goals (try simp only [subFlags_fst_ofNat])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try fv_carry_simp_v1)
  all_goals (
  unfold P_14c_160
  refine ⟨(if x14crdx = 0 then 18446744073709551615#64 else BitVec.ofNat 64 x14crax).toNat, (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x14crcx) &&& 63#32) - 1#64).toNat, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L160
    and_intros
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | with_reducible rfl | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; with_reducible rfl) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact (ofNat_mod64 _).symm) | (simp [setRegF]; done) | (simp [setRegF, BitVec.ofNat_toNat]; done) | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; done) | (simp [setRegF]; bv_omega)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _
    · first | exact hE_x14crbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x14crbx)
    · exact hB_x14crbx
    · first | exact hE_x14crsi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x14crsi)
    · exact hB_x14crsi
    · first | exact hE_x14crdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x14crdi)
    · exact hB_x14crdi
    · first | exact hE_x14cr8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x14cr8)
    · exact hB_x14cr8
    · first | exact hE_x14cr9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x14cr9)
    · exact hB_x14cr9
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x14cm208
    · exact hB_x14cm208
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x14cm210
    · exact hB_x14cm210
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x14cm218
    · exact hB_x14cm218
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x14cm220
    · exact hB_x14cm220
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
