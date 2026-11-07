import Extracted
import Fv256.Arm64.ScanWitA

/-!
# Witness for `SetFromDecimal` (arm64), part B: the `runtime.ifaceeq` and `runtime.cmpstring` contracts

The model implementations of `Janus.Contracts.IfaceSat` (`ifaceeq`, for the interface model `R3 TW`) and
`Janus.Contracts.CmpstringSat` (a byte loop) at the contract addresses of `Extracted.program`, in the closed program
`Extracted.program.ofImpl implA`; the proofs are those of the Janus satisfiability files (the code is position independent).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Map Janus.Spec.Type Janus.Contracts
  Janus.Contracts.Iface Janus.Contracts.IfaceModel Janus.Contracts.Cmpstring Janus.Contracts.IfaceSat Fv256.Arm64.WitModel

namespace Fv256.Arm64.Scan.Witness

set_option maxRecDepth 100000

theorem model_if : Ifaceeq (Extracted.program.ofImpl implA) ifA (R3 TW) := by
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, he3, he4⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hok⟩ := hpre
  by_cases h0 : (s.regs 0).toNat = 0
  · janus_run
    refine rtReturn_of (R3 TW) 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
      rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, he3, he4⟩ ?_
    simp [setReg, ifaceEqual, h0]
  · obtain ⟨-, -, ht0, hok⟩ := hok h0
    obtain ⟨-, ht, hx, hy⟩ := hok ht0
    janus_run
    all_goals
      refine rtReturn_of (R3 TW) 3 [] s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
        rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, he3, he4⟩ ?_
      simp only [ifaceEqual, ht]
      rw [efaceEqual_R3 (g := s.regs 28) ⟨he1, he2, he3, he4⟩ _ _ (by decide)]
      simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
      split
      · rename_i heq; simp [heq]
      · rename_i hne; simp [beq_false_of_ne hne, beq_false_of_ne h0]

open Janus.Contracts.Cmpstring

theorem loop (s : State) (hr1 : (s.regs 30).toNat % 4 = 0) (hr2 : (s.regs 30).toNat < 2 ^ 48) :
    ∀ la (R : Nat → W64) (F : Flags) (a b lb : Nat),
      R 0 = BitVec.ofNat 64 a → R 1 = BitVec.ofNat 64 la → R 2 = BitVec.ofNat 64 b →
      R 3 = BitVec.ofNat 64 lb → la < 2 ^ 64 → lb < 2 ^ 64 →
      R 18 = s.regs 18 → R 28 = s.regs 28 → R 29 = s.regs 29 → R 30 = s.regs 30 →
      StrOK s.mem a la → StrOK s.mem b lb →
      strCmp s.mem a b la lb = strCmp s.mem (s.regs 0).toNat (s.regs 2).toNat (s.regs 1).toNat (s.regs 3).toNat →
      ReachesRet (Extracted.program.ofImpl implA) (s.regs 30) { s with regs := R, flags := F, pc := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } (CmpRet 16 s) := by
  intro la
  induction la with
  | zero =>
    intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
    janus_run [h0, h1, h2, h3, h30]
    all_goals
      apply Janus.Contracts.CmpstringSat.ret_of
      all_goals try (simp only [setReg]; simp [h18, h28, h29])
      simp only [cmpResult]
      rw [← hc]
      clear hc
      cases lb <;> simp_all [strCmp] <;> decide
  | succ la ih =>
    intro R F a b lb h0 h1 h2 h3 hla hlb h18 h28 h29 h30 hsa hsb hc
    rcases hsa with hsa | ⟨hsa1, hsa2⟩
    · omega
    have ha1 : s.mem.accessible a 1 false = true := Memory.accessible_mono _ hsa1 (Nat.le_refl _) (by omega)
    cases lb with
    | zero =>
      janus_run [h0, h1, h2, h3, h30]
      all_goals
        apply Janus.Contracts.CmpstringSat.ret_of
        all_goals try (simp only [setReg]; simp [h18, h28, h29])
        simp only [cmpResult]
        rw [← hc]
        clear hc
        simp [strCmp]
    | succ lb =>
      rcases hsb with hsb | ⟨hsb1, hsb2⟩
      · omega
      have hb1 : s.mem.accessible b 1 false = true := Memory.accessible_mono _ hsb1 (Nat.le_refl _) (by omega)
      have hx : s.mem.readLE a 1 < 256 := by simpa using Memory.readLE_lt s.mem a 1
      have hy : s.mem.readLE b 1 < 256 := by simpa using Memory.readLE_lt s.mem b 1
      janus_run [h0, h1, h2, h3, h30] until [(janus_eval% (Extracted.program.contractAddr "runtime.cmpstring"))]
      all_goals first
        | (apply Janus.Contracts.CmpstringSat.ret_of
           all_goals try (simp only [setReg]; simp [h18, h28, h29])
           simp only [cmpResult]
           rw [← hc]
           clear hc
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
           rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
             Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at *
           rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
             Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at *
           simp only [strCmp]
           split <;> (try split) <;> first | rfl | omega | decide)
        | skip
      rename_i hle
      have heq := hbr
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hle heq
      rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 64)] at heq
      rw [Nat.mod_eq_of_lt (by omega : s.mem.readLE a 1 < 2 ^ 32),
        Nat.mod_eq_of_lt (by omega : s.mem.readLE b 1 < 2 ^ 32)] at heq
      apply ih _ _ (a + 1) (b + 1) lb
      all_goals try (simp only [setReg]; simp [h18, h28, h29, h30])
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · apply BitVec.eq_of_toNat_eq; simp <;> omega
      · omega
      · omega
      · by_cases hl : la = 0
        · exact Or.inl hl
        · exact Or.inr ⟨Memory.accessible_mono _ hsa1 (by omega) (by omega), by omega⟩
      · by_cases hl : lb = 0
        · exact Or.inl hl
        · exact Or.inr ⟨Memory.accessible_mono _ hsb1 (by omega) (by omega), by omega⟩
      · rw [← hc]
        simp only [strCmp, heq, Nat.lt_irrefl, ite_false]

theorem hcmp_lit : CmpstringContract (Extracted.program.ofImpl implA) (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) 16 := by
  intro s hpc ⟨⟨hr1, hr2, _⟩, hsa, hsb⟩
  have key := loop s hr1 hr2 (s.regs 1).toNat s.regs s.flags (s.regs 0).toNat (s.regs 2).toNat
    (s.regs 3).toNat (by simp) (by simp) (by simp) (by simp) (s.regs 1).isLt (s.regs 3).isLt rfl rfl rfl rfl
    hsa hsb rfl
  have hs : ({ s with regs := s.regs, flags := s.flags, pc := BitVec.ofNat 64 (janus_eval% (Extracted.program.contractAddr "runtime.cmpstring")) } : State) = s := by
    cases s; simp only at hpc ⊢; rw [hpc]
  rw [hs] at key
  exact key

theorem hcmp : CmpstringContract (Extracted.program.ofImpl implA) cmA 16 := hcmp_lit

theorem implOK : ImplApart Extracted.program implA := by
  unfold ImplApart; constructor <;> decide

end Fv256.Arm64.Scan.Witness
