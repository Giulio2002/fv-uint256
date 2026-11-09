import Fv256.Proofs.Amd64.R4Tail

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

set_option exponentiation.threshold 400

namespace Fv256.Amd64.R4Seg

def ProbeB (S : State) : Prop := True

theorem add5_val (c0 c1 c2 c3 c4 n0 n1 n2 n3 : Nat) :
    (c0 + n0) % 2 ^ 64 + 2 ^ 64 * ((c1 + n1 + (c0 + n0) / 2 ^ 64) % 2 ^ 64) +
      2 ^ 128 * ((c2 + n2 + (c1 + n1 + (c0 + n0) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64) +
      2 ^ 192 * ((c3 + n3 + (c2 + n2 + (c1 + n1 + (c0 + n0) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64) +
      2 ^ 256 * ((c4 + (c3 + n3 + (c2 + n2 + (c1 + n1 + (c0 + n0) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64) =
    (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 + (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3)) % 2 ^ 320 := by
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem branch (s : State) (hs : R4Pre s) (S : State)
    (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x4ac)) (hR : R4Regs s S) (hM : R4Mem s S.mem)
    (x4acrcx x4acrdx x4acrbx x4acrsi x1cdrdi x4acr8 x4acr9 x47fr11 x33er12 x1cdm60 x1cdm68 x1cdm128 : Nat)
    (hL : L4ac s S x4acrcx x4acrdx x4acrbx x4acrsi x1cdrdi x4acr8 x4acr9 x47fr11 x33er12 x1cdm60 x1cdm68 x1cdm128)
    (hz : x1cdm128 = (s.regs 0).toNat) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x4da)) S (fun S' => ∃ d0 d1 d2 d3 d4,
      TInv s S' d0 d1 d2 d3 d4 x1cdm60 x1cdm68 x33er12 x1cdrdi (s.regs 0).toNat ∧
      d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4 =
        (x4acrcx + 2 ^ 64 * x4acrdx + 2 ^ 128 * x4acrbx + 2 ^ 192 * x4acrsi + 2 ^ 256 * x4acr8 +
          (if x4acr9 = 0 then 0 else x1cdm60 + 2 ^ 64 * x1cdm68 + 2 ^ 128 * x33er12 + 2 ^ 192 * x1cdrdi)) % 2 ^ 320) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz'⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  unfold L4ac at hL
  obtain ⟨e1, b1, e2, b2, e3, b3, e4, b4, e5, b5, e6, b6, e7, b7, e8, b8, e9, b9, e10, b10, e11, b11, e12, b12⟩ := hL
  janus64_run [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, hsp4, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3, Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b5, Nat.mod_eq_of_lt b6, Nat.mod_eq_of_lt b7, Nat.mod_eq_of_lt b8, Nat.mod_eq_of_lt b9, Nat.mod_eq_of_lt b10, Nat.mod_eq_of_lt b11, Nat.mod_eq_of_lt b12] until [0x4b5c9a]
  · -- no borrow: r9 = 0
    have h0 : x4acr9 = 0 := by omega
    refine ⟨x4acrcx, x4acrdx, x4acrbx, x4acrsi, x4acr8, ?_, ?_⟩
    · unfold TInv
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, b1, b2, b3, b4, b6, b10, b11, b9, b5, ?_, ?_, ?_⟩
      · first | rfl | simp [r4Entry]
      · simp [setRegF, e1]
      · simp [setRegF, e2]
      · simp [setRegF, e3]
      · simp [setRegF, e4]
      · simp [setRegF, e6]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, e9]
      · simp [setRegF, e5]
      · exact e12.trans hz
      · unfold R4Regs
        and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
      · exact hM
    · rw [if_pos h0]
      omega
  · have h0 : ¬ x4acr9 = 0 := by omega
    refine ⟨(x4acrcx + x1cdm60) % 2 ^ 64, (x4acrdx + x1cdm68 + (x4acrcx + x1cdm60) / 2 ^ 64) % 2 ^ 64,
      (x4acrbx + x33er12 + (x4acrdx + x1cdm68 + (x4acrcx + x1cdm60) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64,
      (x4acrsi + x1cdrdi + (x4acrbx + x33er12 + (x4acrdx + x1cdm68 + (x4acrcx + x1cdm60) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64,
      (x4acr8 + (x4acrsi + x1cdrdi + (x4acrbx + x33er12 + (x4acrdx + x1cdm68 + (x4acrcx + x1cdm60) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) / 2 ^ 64) % 2 ^ 64, ?_, ?_⟩
    · unfold TInv
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), b10, b11, b9, b5, ?_, ?_, ?_⟩
      · first | rfl | simp [r4Entry]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [← BitVec.ofNat_add, ofNat_mod64]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [ofNat_mod64]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [ofNat_mod64]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [ofNat_mod64]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [ofNat_mod64]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, e9]
      · simp [setRegF, e5]
      · exact e12.trans hz
      · unfold R4Regs
        and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
      · exact hM
    · rw [if_neg h0]
      exact add5_val _ _ _ _ _ _ _ _ _

end Fv256.Amd64.R4Seg
