import Fv256.Amd64.R4Live
import Fv256.Amd64.ReduceSegA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec Fv256.Amd64.ReduceSegA

namespace Fv256.Amd64.R4Seg

/-- the Phase A values (as ofNat witnesses) satisfy the live state at the cut -/
theorem linkA (s S : State) (h : PostA s S) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 x1cdrax x1cdrdx x1cdrsi x1cdrdi x1cdr8 x1cdr9 x1cdr10 x1cdr11 x1cdr13 x1cdr15 x1cdm0 x1cdm8 x1cdm10 x1cdm18 x1cdm20 x1cdm28 x1cdm40 x1cdm48 x1cdm50 x1cdm58 x1cdm60 x1cdm68 x1cdm70 x1cdm78 x1cdm80 x1cdm88 x1cdm90 x1cdm98 x1cdma0 x1cdma8 x1cdmb0 x1cdmb8 x1cdmc0 x1cdmc8 x1cdmd0 x1cdmd8 x1cdme0 x1cdme8 x1cdmf0 x1cdmf8 x1cdm100 x1cdm108 x1cdm110 x1cdm128, L1cd s S x1cdrax x1cdrdx x1cdrsi x1cdrdi x1cdr8 x1cdr9 x1cdr10 x1cdr11 x1cdr13 x1cdr15 x1cdm0 x1cdm8 x1cdm10 x1cdm18 x1cdm20 x1cdm28 x1cdm40 x1cdm48 x1cdm50 x1cdm58 x1cdm60 x1cdm68 x1cdm70 x1cdm78 x1cdm80 x1cdm88 x1cdm90 x1cdm98 x1cdma0 x1cdma8 x1cdmb0 x1cdmb8 x1cdmc0 x1cdmc8 x1cdmd0 x1cdmd8 x1cdme0 x1cdme8 x1cdmf0 x1cdmf8 x1cdm100 x1cdm108 x1cdm110 x1cdm128 ∧ R4Regs s S ∧ R4Mem s S.mem ∧
      (x1cdrax = v0 % 18446744073709551616 ∧ x1cdrdx = v2 % 18446744073709551616 ∧ x1cdrsi = v4 % 18446744073709551616 ∧ x1cdrdi = v5 % 18446744073709551616 ∧ x1cdr8 = v6 % 18446744073709551616 ∧ x1cdr9 = v7 % 18446744073709551616 ∧ x1cdr10 = v8 % 18446744073709551616 ∧ x1cdr11 = v9 % 18446744073709551616 ∧ x1cdr13 = v11 % 18446744073709551616 ∧ x1cdr15 = v12 % 18446744073709551616 ∧ x1cdm0 = v41 % 18446744073709551616 ∧ x1cdm8 = v40 % 18446744073709551616 ∧ x1cdm10 = v39 % 18446744073709551616 ∧ x1cdm18 = v14 % 18446744073709551616 ∧ x1cdm20 = v16 % 18446744073709551616 ∧ x1cdm28 = v18 % 18446744073709551616 ∧ x1cdm40 = v30 % 18446744073709551616 ∧ x1cdm48 = v23 % 18446744073709551616 ∧ x1cdm50 = v17 % 18446744073709551616 ∧ x1cdm58 = v15 % 18446744073709551616 ∧ x1cdm60 = v46 % 18446744073709551616 ∧ x1cdm68 = v45 % 18446744073709551616 ∧ x1cdm70 = v44 % 18446744073709551616 ∧ x1cdm78 = v43 % 18446744073709551616 ∧ x1cdm80 = v42 % 18446744073709551616 ∧ x1cdm88 = v38 % 18446744073709551616 ∧ x1cdm90 = v37 % 18446744073709551616 ∧ x1cdm98 = v36 % 18446744073709551616 ∧ x1cdma0 = v35 % 18446744073709551616 ∧ x1cdma8 = v34 % 18446744073709551616 ∧ x1cdmb0 = v33 % 18446744073709551616 ∧ x1cdmb8 = v32 % 18446744073709551616 ∧ x1cdmc0 = v31 % 18446744073709551616 ∧ x1cdmc8 = v29 % 18446744073709551616 ∧ x1cdmd0 = v28 % 18446744073709551616 ∧ x1cdmd8 = v27 % 18446744073709551616 ∧ x1cdme0 = v26 % 18446744073709551616 ∧ x1cdme8 = v25 % 18446744073709551616 ∧ x1cdmf0 = v24 % 18446744073709551616 ∧ x1cdmf8 = v22 % 18446744073709551616 ∧ x1cdm100 = v21 % 18446744073709551616 ∧ x1cdm108 = v20 % 18446744073709551616 ∧ x1cdm110 = v19 % 18446744073709551616 ∧ x1cdm128 = v13 % 18446744073709551616) ∧
      (v0 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 ∧ v1 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8 ∧ v2 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 / 18446744073709551616 ∧ v3 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8 ∧ v4 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 24) 8 / 18446744073709551616 ∧ v5 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 24) 8 ∧ v6 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 / 18446744073709551616 ∧ v7 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 / 18446744073709551616 ∧ v8 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 / 18446744073709551616 ∧ v9 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 ∧ v10 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8 ∧ v11 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7)) 8 / 18446744073709551616 ∧ v12 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7)) 8 ∧ v13 = BitVec.toNat (s.regs 0) ∧ v14 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 24) 8 ∧ v15 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7)) 8 / 18446744073709551616 ∧ v16 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 8) 8 / 18446744073709551616 ∧ v17 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 8) 8 / 18446744073709551616 ∧ v18 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 8) 8 ∧ v19 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 8) 8 / 18446744073709551616 ∧ v20 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 8) 8 ∧ v21 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 / 18446744073709551616 ∧ v22 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 ∧ v23 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 / 18446744073709551616 ∧ v24 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 ∧ v25 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 / 18446744073709551616 ∧ v26 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 ∧ v27 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 24) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 / 18446744073709551616 ∧ v28 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 / 18446744073709551616 ∧ v29 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 ∧ v30 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 / 18446744073709551616 ∧ v31 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 ∧ v32 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 / 18446744073709551616 ∧ v33 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 ∧ v34 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 24) 8 ∧ v35 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 40) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 ∧ v36 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 56) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 ∧ v37 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 48) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 32) 8 ∧ v38 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8 ∧ v39 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 8) 8 ∧ v40 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 16) 8 ∧ v41 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 ∧ v42 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 16) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 / 18446744073709551616 ∧ v43 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3) + 32) 8 * Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 7) + 24) 8 / 18446744073709551616 ∧ v44 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 16) 8 ∧ v45 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1) + 8) 8 ∧ v46 = Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 8) := by
  unfold PostA at h
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, hh⟩ := h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80, f81, f82, f83, f84, f85, f86, f87, f88, f89, f90, f91, f92, f93, hR, hrb, hF⟩ := hh
  refine ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v0 % 18446744073709551616, v2 % 18446744073709551616, v4 % 18446744073709551616, v5 % 18446744073709551616, v6 % 18446744073709551616, v7 % 18446744073709551616, v8 % 18446744073709551616, v9 % 18446744073709551616, v11 % 18446744073709551616, v12 % 18446744073709551616, v41 % 18446744073709551616, v40 % 18446744073709551616, v39 % 18446744073709551616, v14 % 18446744073709551616, v16 % 18446744073709551616, v18 % 18446744073709551616, v30 % 18446744073709551616, v23 % 18446744073709551616, v17 % 18446744073709551616, v15 % 18446744073709551616, v46 % 18446744073709551616, v45 % 18446744073709551616, v44 % 18446744073709551616, v43 % 18446744073709551616, v42 % 18446744073709551616, v38 % 18446744073709551616, v37 % 18446744073709551616, v36 % 18446744073709551616, v35 % 18446744073709551616, v34 % 18446744073709551616, v33 % 18446744073709551616, v32 % 18446744073709551616, v31 % 18446744073709551616, v29 % 18446744073709551616, v28 % 18446744073709551616, v27 % 18446744073709551616, v26 % 18446744073709551616, v25 % 18446744073709551616, v24 % 18446744073709551616, v22 % 18446744073709551616, v21 % 18446744073709551616, v20 % 18446744073709551616, v19 % 18446744073709551616, v13 % 18446744073709551616, ?_, ?_, ?_, ?_, ?_⟩
  · unfold L1cd
    and_intros
    · rw [ofNat_mod64]; exact f0
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f4
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f8
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f10
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f12
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f14
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f16
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f18
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f22
    · exact Nat.mod_lt _ (by decide)
    · rw [ofNat_mod64]; exact f24
    · exact Nat.mod_lt _ (by decide)
    · exact f82
    · exact Nat.mod_lt _ (by decide)
    · exact f80
    · exact Nat.mod_lt _ (by decide)
    · exact f78
    · exact Nat.mod_lt _ (by decide)
    · exact f28
    · exact Nat.mod_lt _ (by decide)
    · exact f32
    · exact Nat.mod_lt _ (by decide)
    · exact f36
    · exact Nat.mod_lt _ (by decide)
    · exact f60
    · exact Nat.mod_lt _ (by decide)
    · exact f46
    · exact Nat.mod_lt _ (by decide)
    · exact f34
    · exact Nat.mod_lt _ (by decide)
    · exact f30
    · exact Nat.mod_lt _ (by decide)
    · exact f92
    · exact Nat.mod_lt _ (by decide)
    · exact f90
    · exact Nat.mod_lt _ (by decide)
    · exact f88
    · exact Nat.mod_lt _ (by decide)
    · exact f86
    · exact Nat.mod_lt _ (by decide)
    · exact f84
    · exact Nat.mod_lt _ (by decide)
    · exact f76
    · exact Nat.mod_lt _ (by decide)
    · exact f74
    · exact Nat.mod_lt _ (by decide)
    · exact f72
    · exact Nat.mod_lt _ (by decide)
    · exact f70
    · exact Nat.mod_lt _ (by decide)
    · exact f68
    · exact Nat.mod_lt _ (by decide)
    · exact f66
    · exact Nat.mod_lt _ (by decide)
    · exact f64
    · exact Nat.mod_lt _ (by decide)
    · exact f62
    · exact Nat.mod_lt _ (by decide)
    · exact f58
    · exact Nat.mod_lt _ (by decide)
    · exact f56
    · exact Nat.mod_lt _ (by decide)
    · exact f54
    · exact Nat.mod_lt _ (by decide)
    · exact f52
    · exact Nat.mod_lt _ (by decide)
    · exact f50
    · exact Nat.mod_lt _ (by decide)
    · exact f48
    · exact Nat.mod_lt _ (by decide)
    · exact f44
    · exact Nat.mod_lt _ (by decide)
    · exact f42
    · exact Nat.mod_lt _ (by decide)
    · exact f40
    · exact Nat.mod_lt _ (by decide)
    · exact f38
    · exact Nat.mod_lt _ (by decide)
    · exact f26
    · exact Nat.mod_lt _ (by decide)
  · exact hR
  · exact ⟨hF, hrb⟩
  · and_intros <;> rfl
  · and_intros
    · exact f1
    · exact f3
    · exact f5
    · exact f7
    · exact f9
    · exact f11
    · exact f13
    · exact f15
    · exact f17
    · exact f19
    · exact f21
    · exact f23
    · exact f25
    · exact f27
    · exact f29
    · exact f31
    · exact f33
    · exact f35
    · exact f37
    · exact f39
    · exact f41
    · exact f43
    · exact f45
    · exact f47
    · exact f49
    · exact f51
    · exact f53
    · exact f55
    · exact f57
    · exact f59
    · exact f61
    · exact f63
    · exact f65
    · exact f67
    · exact f69
    · exact f71
    · exact f73
    · exact f75
    · exact f77
    · exact f79
    · exact f81
    · exact f83
    · exact f85
    · exact f87
    · exact f89
    · exact f91
    · exact f93

end Fv256.Amd64.R4Seg
