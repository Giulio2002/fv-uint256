import Extracted
import Fv256.Proofs.Amd64.SfdWitA

/-!
# Witness for `SetFromDecimal` (amd64), part B: the `runtime.ifaceeq` and `runtime.cmpstring` contracts

The model implementations of `Janus.Contracts.IfaceSatAmd64` (`ifaceeq`, for the interface model `R0`) and
`Janus.Contracts.CmpstringSatAmd64` (a byte loop) at the contract addresses of `Extracted.program`, in the linked program
`Extracted.program.link implA`; the proofs are those of the Janus satisfiability files (the code is position independent).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type Janus.Contracts
  Janus.Contracts.IfaceAmd64 Janus.Contracts.IfaceModel Janus.Contracts.Cmpstring Janus.Contracts.IfaceSatAmd64
  Janus.Contracts.CmpstringSatAmd64
  Janus.Contracts.Iface

namespace Fv256.Amd64.SetFromDecimal.Witness

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem model_if : Ifaceeq (Extracted.program.link implA) ifA R0 := by
  rw [linked_eq]
  intro s hpc ⟨hpre, hok⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  by_cases h0 : (s.regs 0).toNat = 0
  · janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp [setRegF, ifaceEqual, h0]
  · obtain ⟨-, -, ht0, hok⟩ := hok h0
    obtain ⟨-, ht, hx, hy⟩ := hok ht0
    janus64_run
    all_goals
      refine rtReturn_of R0 3 [] s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
        (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
      simp only [ifaceEqual, ht]
      rw [Janus.Contracts.IfaceSat.efaceEqual_R0 (g := s.regs 14) ⟨he1, he2, hd⟩]
      simp only [setRegF, reduceIte, Nat.reduceEqDiff, setcc_low_byte, beq_false_of_ne h0,
        Bool.false_or]
      have ha := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 1).toNat 8
      have hb := Janus.Arm64.Memory.readLE_lt s.mem (s.regs 3).toNat 8
      simp only [Nat.reducePow] at ha hb
      split
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 =
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [this]
      · rename_i h
        have : Janus.Arm64.Memory.readLE s.mem (s.regs 3).toNat 8 ≠
            Janus.Arm64.Memory.readLE s.mem (s.regs 1).toNat 8 := by omega
        simp [beq_false_of_ne this]


/-- The return of the implementation as `CmpRet64`. -/
theorem ret_of (s : State) (R : Nat → W64) (F : Flags) (hR0 : R 0 = cmpResult64 s)
    (h4 : R 4 = s.regs 4 + 8#64) (h5 : R 5 = s.regs 5) (h14 : R 14 = s.regs 14) :
    CmpRet64 16 s { s with regs := R, flags := F, rip := retAddrOf s } := by
  refine ⟨R, F, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _⟩
  simp only [retState64]
  congr 1
  · funext i
    simp only [callRegs64]
    by_cases e4 : i = 4
    · subst e4; simp [h4]
    by_cases e5 : i = 5 ∨ i = 14
    · rcases e5 with rfl | rfl <;> simp [h5, h14]
    simp only [e4, e5, ite_false]
    by_cases e0 : i = 0
    · subst e0; simp [hR0]
    by_cases e3 : i = 3
    · subst e3; simp
    by_cases e1 : i = 1
    · subst e1; simp
    simp [e0, e3, e1]
  · funext i; split <;> simp_all

/-- The loop, from its head with `la` bytes of `a` left. -/
theorem loop (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (hacc : s.mem.accessible (s.regs 4).toNat 8 false = true) (hnw : (s.regs 4).toNat + 8 ≤ 2 ^ 48) :
    ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
      R 0 = BitVec.ofNat 64 a → R 3 = BitVec.ofNat 64 la → R 1 = BitVec.ofNat 64 b →
      R 7 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
      R 4 = s.regs 4 → R 5 = s.regs 5 → R 14 = s.regs 14 →
      StrOK s.mem a la → StrOK s.mem b lb →
      strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat →
      ReachesRet linked (retAddrOf s) { s with regs := R, flags := F, rip := BitVec.ofNat 64 4204160 } (CmpRet64 16 s) := by
  intro la
  induction la with
  | zero =>
    intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
    janus64_run [h0, h1, h3, h7, h4]
    all_goals
      apply ret_of
      all_goals try (simp only [setRegF]; simp [h4, h5, h14])
      simp only [cmpResult64]
      rw [← hc]
      clear hc
      cases lb <;> simp_all [strCmp] <;> decide
  | succ la ih =>
    intro R F a b lb h0 h3 h1 h7 hla hlb h4 h5 h14 hsa hsb hc
    rcases hsa with hsa | ⟨hsa1, hsa2⟩
    · omega
    have ha1 : s.mem.accessible a 1 false = true :=
      Janus.Arm64.Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
    cases lb with
    | zero =>
      janus64_run [h0, h1, h3, h7, h4]
      all_goals
        apply ret_of
        all_goals try (simp only [setRegF]; simp [h4, h5, h14])
        simp only [cmpResult64]
        rw [← hc]
        clear hc
        simp [strCmp]
    | succ lb =>
      rcases hsb with hsb | ⟨hsb1, hsb2⟩
      · omega
      have hb1 : s.mem.accessible b 1 false = true :=
        Janus.Arm64.Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
      have hx : s.mem.readLE a 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem a 1
      have hy : s.mem.readLE b 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem b 1
      have e : ∀ x, x < 256 → BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x)))
          = BitVec.ofNat 32 x := by
        intro x hx; apply BitVec.eq_of_toNat_eq; simp; omega
      have hsub : (BitVec.ofNat 32 (s.mem.readLE a 1) - BitVec.ofNat 32 (s.mem.readLE b 1) = 0#32) ↔
          s.mem.readLE a 1 = s.mem.readLE b 1 := by
        constructor
        · intro h; have := congrArg BitVec.toNat h
          simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega
        · intro h; rw [h]; simp
      janus64_run [h0, h1, h3, h7, h4] until [4204160]
      all_goals simp only [e _ hx, e _ hy, hsub, Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 4294967296),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 4294967296)] at *
      all_goals first
        | (apply ret_of
           all_goals try (simp only [setRegF]; simp [h4, h5, h14])
           simp only [cmpResult64]
           rw [← hc]
           clear hc
           simp only [strCmp]
           split <;> (try split) <;> first | rfl | omega | decide)
        | skip
      apply ih _ _ (a + 1) (b + 1) lb
      all_goals try (simp only [setRegF]; simp [h4, h5, h14])
      all_goals first
        | (apply BitVec.eq_of_toNat_eq; simp <;> omega)
        | omega
        | (by_cases hl : la = 0
           · exact Or.inl hl
           · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩)
        | (by_cases hl : lb = 0
           · exact Or.inl hl
           · exact Or.inr ⟨Janus.Arm64.Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩)
        | (rw [← hc]; simp only [strCmp, hbr, Nat.lt_irrefl, ite_false])

/-- The byte loop meets the contract. -/
theorem hcmp : CmpstringContract64 (Extracted.program.link implA) cmA 16 := by
  rw [linked_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, hsa, hsb⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have key := loop s hr hacc (by omega) (s.regs 3).toNat s.regs s.flags (s.regs 0).toNat (s.regs 1).toNat
    (s.regs 7).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 3).isLt (s.regs 7).isLt rfl rfl rfl
    hsa hsb rfl
  have hs : ({ s with regs := s.regs, flags := s.flags, rip := BitVec.ofNat 64 4204160 } : State) = s := by
    cases s; simp only at hpc ⊢; rw [hpc]
  rw [hs] at key
  exact key


end Fv256.Amd64.SetFromDecimal.Witness
