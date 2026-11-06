import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c1_4 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 3 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 4)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 60 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 4 := Util.bitLen_of_range _ 4 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980064 32 = 100000000000000000000 := by simpa using hTB.2 0 (by decide)
  have hTa : s.mem.accessible 5980064 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980064
  have hl1 := Util.readLE8_lt s.mem 5980072
  have hl2 := Util.readLE8_lt s.mem 5980080
  have hl3 := Util.readLE8_lt s.mem 5980088
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980064 7766279631452241920 5 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980072 8 = 5 := hT1'
  have hT2 : s.mem.readLE 5980080 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980088 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980064 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 7766279631452241920 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980064 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980072 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980072 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980080 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980080 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980088 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980088 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_5 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 4 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 5)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 59 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 5 := Util.bitLen_of_range _ 5 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980096 32 = 1000000000000000000000 := by simpa using hTB.2 1 (by decide)
  have hTa : s.mem.accessible 5980096 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980096
  have hl1 := Util.readLE8_lt s.mem 5980104
  have hl2 := Util.readLE8_lt s.mem 5980112
  have hl3 := Util.readLE8_lt s.mem 5980120
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980096 3875820019684212736 54 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980104 8 = 54 := hT1'
  have hT2 : s.mem.readLE 5980112 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980120 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980096 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 3875820019684212736 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980096 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980104 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980104 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980112 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980112 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980120 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980120 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_6 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 5 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 6)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 58 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 6 := Util.bitLen_of_range _ 6 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980096 32 = 1000000000000000000000 := by simpa using hTB.2 1 (by decide)
  have hTa : s.mem.accessible 5980096 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980096
  have hl1 := Util.readLE8_lt s.mem 5980104
  have hl2 := Util.readLE8_lt s.mem 5980112
  have hl3 := Util.readLE8_lt s.mem 5980120
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980096 3875820019684212736 54 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980104 8 = 54 := hT1'
  have hT2 : s.mem.readLE 5980112 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980120 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980096 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 3875820019684212736 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980096 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980104 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980104 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980112 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980112 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980120 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980120 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_7 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 6 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 7)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 57 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 7 := Util.bitLen_of_range _ 7 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980096 32 = 1000000000000000000000 := by simpa using hTB.2 1 (by decide)
  have hTa : s.mem.accessible 5980096 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980096
  have hl1 := Util.readLE8_lt s.mem 5980104
  have hl2 := Util.readLE8_lt s.mem 5980112
  have hl3 := Util.readLE8_lt s.mem 5980120
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980096 3875820019684212736 54 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980104 8 = 54 := hT1'
  have hT2 : s.mem.readLE 5980112 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980120 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980096 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 3875820019684212736 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980096 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980104 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980104 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980112 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980112 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980120 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980120 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_8 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 7 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 8)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 56 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 8 := Util.bitLen_of_range _ 8 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980096 32 = 1000000000000000000000 := by simpa using hTB.2 1 (by decide)
  have hTa : s.mem.accessible 5980096 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980096
  have hl1 := Util.readLE8_lt s.mem 5980104
  have hl2 := Util.readLE8_lt s.mem 5980112
  have hl3 := Util.readLE8_lt s.mem 5980120
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980096 3875820019684212736 54 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980104 8 = 54 := hT1'
  have hT2 : s.mem.readLE 5980112 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980120 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980096 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 3875820019684212736 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980096 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980104 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980104 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980112 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980112 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980120 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980120 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_9 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 8 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 9)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 55 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 9 := Util.bitLen_of_range _ 9 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980128 32 = 10000000000000000000000 := by simpa using hTB.2 2 (by decide)
  have hTa : s.mem.accessible 5980128 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980128
  have hl1 := Util.readLE8_lt s.mem 5980136
  have hl2 := Util.readLE8_lt s.mem 5980144
  have hl3 := Util.readLE8_lt s.mem 5980152
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980128 1864712049423024128 542 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980136 8 = 542 := hT1'
  have hT2 : s.mem.readLE 5980144 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980152 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980128 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1864712049423024128 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980128 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980136 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980136 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980144 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980144 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980152 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980152 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_10 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 9 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 10)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 54 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 10 := Util.bitLen_of_range _ 10 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980128 32 = 10000000000000000000000 := by simpa using hTB.2 2 (by decide)
  have hTa : s.mem.accessible 5980128 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980128
  have hl1 := Util.readLE8_lt s.mem 5980136
  have hl2 := Util.readLE8_lt s.mem 5980144
  have hl3 := Util.readLE8_lt s.mem 5980152
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980128 1864712049423024128 542 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980136 8 = 542 := hT1'
  have hT2 : s.mem.readLE 5980144 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980152 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980128 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1864712049423024128 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980128 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980136 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980136 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980144 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980144 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980152 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980152 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_11 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 10 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 11)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 53 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 11 := Util.bitLen_of_range _ 11 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980128 32 = 10000000000000000000000 := by simpa using hTB.2 2 (by decide)
  have hTa : s.mem.accessible 5980128 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980128
  have hl1 := Util.readLE8_lt s.mem 5980136
  have hl2 := Util.readLE8_lt s.mem 5980144
  have hl3 := Util.readLE8_lt s.mem 5980152
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980128 1864712049423024128 542 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980136 8 = 542 := hT1'
  have hT2 : s.mem.readLE 5980144 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980152 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980128 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1864712049423024128 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980128 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980136 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980136 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980144 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980144 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980152 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980152 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_12 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 11 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 12)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 52 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 12 := Util.bitLen_of_range _ 12 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980160 32 = 100000000000000000000000 := by simpa using hTB.2 3 (by decide)
  have hTa : s.mem.accessible 5980160 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980160
  have hl1 := Util.readLE8_lt s.mem 5980168
  have hl2 := Util.readLE8_lt s.mem 5980176
  have hl3 := Util.readLE8_lt s.mem 5980184
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980160 200376420520689664 5421 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980168 8 = 5421 := hT1'
  have hT2 : s.mem.readLE 5980176 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980184 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980160 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 200376420520689664 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980160 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980168 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980168 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980176 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980176 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980184 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980184 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_13 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 12 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 13)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 51 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 13 := Util.bitLen_of_range _ 13 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980160 32 = 100000000000000000000000 := by simpa using hTB.2 3 (by decide)
  have hTa : s.mem.accessible 5980160 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980160
  have hl1 := Util.readLE8_lt s.mem 5980168
  have hl2 := Util.readLE8_lt s.mem 5980176
  have hl3 := Util.readLE8_lt s.mem 5980184
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980160 200376420520689664 5421 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980168 8 = 5421 := hT1'
  have hT2 : s.mem.readLE 5980176 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980184 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980160 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 200376420520689664 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980160 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980168 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980168 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980176 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980176 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980184 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980184 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_14 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 13 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 14)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 50 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 14 := Util.bitLen_of_range _ 14 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980160 32 = 100000000000000000000000 := by simpa using hTB.2 3 (by decide)
  have hTa : s.mem.accessible 5980160 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980160
  have hl1 := Util.readLE8_lt s.mem 5980168
  have hl2 := Util.readLE8_lt s.mem 5980176
  have hl3 := Util.readLE8_lt s.mem 5980184
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980160 200376420520689664 5421 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980168 8 = 5421 := hT1'
  have hT2 : s.mem.readLE 5980176 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980184 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980160 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 200376420520689664 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980160 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980168 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980168 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980176 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980176 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980184 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980184 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_15 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 14 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 15)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 49 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 15 := Util.bitLen_of_range _ 15 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980192 32 = 1000000000000000000000000 := by simpa using hTB.2 4 (by decide)
  have hTa : s.mem.accessible 5980192 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980192
  have hl1 := Util.readLE8_lt s.mem 5980200
  have hl2 := Util.readLE8_lt s.mem 5980208
  have hl3 := Util.readLE8_lt s.mem 5980216
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980192 2003764205206896640 54210 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980200 8 = 54210 := hT1'
  have hT2 : s.mem.readLE 5980208 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980216 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980192 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2003764205206896640 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980192 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980200 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980200 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980208 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980208 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980216 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980216 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_16 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 15 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 16)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 48 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 16 := Util.bitLen_of_range _ 16 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980192 32 = 1000000000000000000000000 := by simpa using hTB.2 4 (by decide)
  have hTa : s.mem.accessible 5980192 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980192
  have hl1 := Util.readLE8_lt s.mem 5980200
  have hl2 := Util.readLE8_lt s.mem 5980208
  have hl3 := Util.readLE8_lt s.mem 5980216
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980192 2003764205206896640 54210 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980200 8 = 54210 := hT1'
  have hT2 : s.mem.readLE 5980208 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980216 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980192 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2003764205206896640 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980192 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980200 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980200 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980208 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980208 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980216 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980216 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_17 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 16 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 17)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 47 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 17 := Util.bitLen_of_range _ 17 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980192 32 = 1000000000000000000000000 := by simpa using hTB.2 4 (by decide)
  have hTa : s.mem.accessible 5980192 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980192
  have hl1 := Util.readLE8_lt s.mem 5980200
  have hl2 := Util.readLE8_lt s.mem 5980208
  have hl3 := Util.readLE8_lt s.mem 5980216
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980192 2003764205206896640 54210 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980200 8 = 54210 := hT1'
  have hT2 : s.mem.readLE 5980208 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980216 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980192 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2003764205206896640 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980192 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980200 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980200 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980208 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980208 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980216 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980216 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_18 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 17 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 18)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 46 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 18 := Util.bitLen_of_range _ 18 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980192 32 = 1000000000000000000000000 := by simpa using hTB.2 4 (by decide)
  have hTa : s.mem.accessible 5980192 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980192
  have hl1 := Util.readLE8_lt s.mem 5980200
  have hl2 := Util.readLE8_lt s.mem 5980208
  have hl3 := Util.readLE8_lt s.mem 5980216
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980192 2003764205206896640 54210 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980200 8 = 54210 := hT1'
  have hT2 : s.mem.readLE 5980208 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980216 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980192 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2003764205206896640 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980192 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980200 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980200 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980208 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980208 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980216 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980216 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_19 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 18 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 19)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 45 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 19 := Util.bitLen_of_range _ 19 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980224 32 = 10000000000000000000000000 := by simpa using hTB.2 5 (by decide)
  have hTa : s.mem.accessible 5980224 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980224
  have hl1 := Util.readLE8_lt s.mem 5980232
  have hl2 := Util.readLE8_lt s.mem 5980240
  have hl3 := Util.readLE8_lt s.mem 5980248
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980224 1590897978359414784 542101 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980232 8 = 542101 := hT1'
  have hT2 : s.mem.readLE 5980240 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980248 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980224 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1590897978359414784 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980224 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980232 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980232 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980240 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980240 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980248 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980248 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c1_20 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 19 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 20)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 44 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 20 := Util.bitLen_of_range _ 20 (by omega) (by omega) (by omega)
    omega
  have hwr : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (s.regs 4).toNat 8) = s.mem.readLE (s.regs 4).toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE x.toNat 8) = s.mem.readLE x.toNat 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 8) 8) = s.mem.readLE (x.toNat + 8) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 16) 8) = s.mem.readLE (x.toNat + 16) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hw3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE (x.toNat + 24) 8) = s.mem.readLE (x.toNat + 24) 8 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  have hTv : s.mem.readLE 5980224 32 = 10000000000000000000000000 := by simpa using hTB.2 5 (by decide)
  have hTa : s.mem.accessible 5980224 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980224
  have hl1 := Util.readLE8_lt s.mem 5980232
  have hl2 := Util.readLE8_lt s.mem 5980240
  have hl3 := Util.readLE8_lt s.mem 5980248
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980224 1590897978359414784 542101 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980232 8 = 542101 := hT1'
  have hT2 : s.mem.readLE 5980240 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980248 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980224 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1590897978359414784 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980224 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980232 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980232 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980240 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980240 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980248 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980248 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 8) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hz2, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

end Fv256.Amd64.Log10
