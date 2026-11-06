import Fv256.Amd64.R4Live

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

def P_33e_38b (s : State) (x33erax x33ercx x33erbx x33ersi x33erdi x33er8 x33er9 x33er10 x33er11 x33er12 x33er13 x33er15 x33em0 x33em8 x33em10 x33em18 x33em20 x33em28 x33em60 x33em68 x33em88 x33em128 : Nat) (S' : State) : Prop :=
  ∃ x38bm30 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110, L38b s S' x33ercx x33erbx x33ersi x33erdi x33er8 x33er9 x33er10 x33er11 x33er12 x33er13 x33er15 x33em0 x33em8 x33em10 x33em18 x33em20 x33em28 x38bm30 x33em60 x33em68 x33em88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x33em128 ∧ x38bm30 = (x33em68 * x33erbx) % 18446744073709551616 ∧ x38bme8 = (x33em68 * x33ersi) % 18446744073709551616 ∧ x38bmf0 = (x33em68 * x33ersi / 18446744073709551616) % 18446744073709551616 ∧ x38bmf8 = (x33em68 * x33ercx) % 18446744073709551616 ∧ x38bm100 = (x33em68 * x33ercx / 18446744073709551616) % 18446744073709551616 ∧ x38bm108 = (x33em68 * x33erbx / 18446744073709551616) % 18446744073709551616 ∧ x38bm110 = x33erax % 18446744073709551616 ∧ R4Regs s S' ∧ R4Mem s S'.mem

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem g_33e_38b (s S : State) (hpc : S.rip = BitVec.ofNat 64 (r4Entry + 0x33e)) (hs : R4Pre s)
    (hR : R4Regs s S) (hM : R4Mem s S.mem) (x33erax x33ercx x33erbx x33ersi x33erdi x33er8 x33er9 x33er10 x33er11 x33er12 x33er13 x33er15 x33em0 x33em8 x33em10 x33em18 x33em20 x33em28 x33em60 x33em68 x33em88 x33em128 : Nat) (hL : L33e s S x33erax x33ercx x33erbx x33ersi x33erdi x33er8 x33er9 x33er10 x33er11 x33er12 x33er13 x33er15 x33em0 x33em8 x33em10 x33em18 x33em20 x33em28 x33em60 x33em68 x33em88 x33em128) :
    ReachesRet Fv256.ReduceProg.program (BitVec.ofNat 64 (r4Entry + 0x38b)) S (P_33e_38b s  x33erax x33ercx x33erbx x33ersi x33erdi x33er8 x33er9 x33er10 x33er11 x33er12 x33er13 x33er15 x33em0 x33em8 x33em10 x33em18 x33em20 x33em28 x33em60 x33em68 x33em88 x33em128) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
  clear hmu hm3 hdz hdx hdm hdu hdg
  obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
  have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  obtain ⟨hE_x33erax, hB_x33erax, hE_x33ercx, hB_x33ercx, hE_x33erbx, hB_x33erbx, hE_x33ersi, hB_x33ersi, hE_x33erdi, hB_x33erdi, hE_x33er8, hB_x33er8, hE_x33er9, hB_x33er9, hE_x33er10, hB_x33er10, hE_x33er11, hB_x33er11, hE_x33er12, hB_x33er12, hE_x33er13, hB_x33er13, hE_x33er15, hB_x33er15, hE_x33em0, hB_x33em0, hE_x33em8, hB_x33em8, hE_x33em10, hB_x33em10, hE_x33em18, hB_x33em18, hE_x33em20, hB_x33em20, hE_x33em28, hB_x33em28, hE_x33em60, hB_x33em60, hE_x33em68, hB_x33em68, hE_x33em88, hB_x33em88, hE_x33em128, hB_x33em128⟩ := hL
  janus64_run [Util.readLE_32, hE_x33erax, hE_x33ercx, hE_x33erbx, hE_x33ersi, hE_x33erdi, hE_x33er8, hE_x33er9, hE_x33er10, hE_x33er11, hE_x33er12, hE_x33er13, hE_x33er15, hE_x33em0, hE_x33em8, hE_x33em10, hE_x33em18, hE_x33em20, hE_x33em28, hE_x33em60, hE_x33em68, hE_x33em88, hE_x33em128, hsp4, Nat.mod_eq_of_lt hB_x33erax, Nat.mod_eq_of_lt hB_x33ercx, Nat.mod_eq_of_lt hB_x33erbx, Nat.mod_eq_of_lt hB_x33ersi, Nat.mod_eq_of_lt hB_x33erdi, Nat.mod_eq_of_lt hB_x33er8, Nat.mod_eq_of_lt hB_x33er9, Nat.mod_eq_of_lt hB_x33er10, Nat.mod_eq_of_lt hB_x33er11, Nat.mod_eq_of_lt hB_x33er12, Nat.mod_eq_of_lt hB_x33er13, Nat.mod_eq_of_lt hB_x33er15, Nat.mod_eq_of_lt hB_x33em0, Nat.mod_eq_of_lt hB_x33em8, Nat.mod_eq_of_lt hB_x33em10, Nat.mod_eq_of_lt hB_x33em18, Nat.mod_eq_of_lt hB_x33em20, Nat.mod_eq_of_lt hB_x33em28, Nat.mod_eq_of_lt hB_x33em60, Nat.mod_eq_of_lt hB_x33em68, Nat.mod_eq_of_lt hB_x33em88, Nat.mod_eq_of_lt hB_x33em128]
  all_goals (try janus_carry_simp)
  all_goals (try simp only [subFlags_fst_ofNat, zero_sub64])
  all_goals (try simp only [← BitVec.ofNat_add])
  all_goals (try janus_carry_simp)
  all_goals (
  unfold P_33e_38b
  refine ⟨(x33em68 * x33erbx) % 18446744073709551616, (x33em68 * x33ersi) % 18446744073709551616, (x33em68 * x33ersi / 18446744073709551616) % 18446744073709551616, (x33em68 * x33ercx) % 18446744073709551616, (x33em68 * x33ercx / 18446744073709551616) % 18446744073709551616, (x33em68 * x33erbx / 18446744073709551616) % 18446744073709551616, x33erax % 18446744073709551616, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L38b
    and_intros
    · first | exact hE_x33ercx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33ercx)
    · exact hB_x33ercx
    · first | exact hE_x33erbx | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33erbx)
    · exact hB_x33erbx
    · first | exact hE_x33ersi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33ersi)
    · exact hB_x33ersi
    · first | exact hE_x33erdi | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33erdi)
    · exact hB_x33erdi
    · first | exact hE_x33er8 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er8)
    · exact hB_x33er8
    · first | exact hE_x33er9 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er9)
    · exact hB_x33er9
    · first | exact hE_x33er10 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er10)
    · exact hB_x33er10
    · first | exact hE_x33er11 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er11)
    · exact hB_x33er11
    · first | exact hE_x33er12 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er12)
    · exact hB_x33er12
    · first | exact hE_x33er13 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er13)
    · exact hB_x33er13
    · first | exact hE_x33er15 | (simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; exact hE_x33er15)
    · exact hB_x33er15
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em0
    · exact hB_x33em0
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em8
    · exact hB_x33em8
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em10
    · exact hB_x33em10
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em18
    · exact hB_x33em18
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em20
    · exact hB_x33em20
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em28
    · exact hB_x33em28
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em60
    · exact hB_x33em60
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em68
    · exact hB_x33em68
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em88
    · exact hB_x33em88
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
    · first | with_reducible rfl | (simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow, Nat.mod_mod]; done)
    · first | exact Nat.mod_lt _ (by decide) | exact BitVec.isLt _ | (split <;> decide)
    · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hE_x33em128
    · exact hB_x33em128
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · with_reducible rfl
  · unfold R4Regs
    and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
  · repeat (refine R4Mem.write ?_ _ _ _ ?_ ?_)
    all_goals first | exact hM | omega
  )

end Fv256.Amd64.R4Seg
