import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c1_55 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 54 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 55)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 9 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 55 := Util.bitLen_of_range _ 55 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980576 32 = 1000000000000000000000000000000000000 := by simpa using hTB.2 16 (by decide)
  have hTa : s.mem.accessible 5980576 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980576
  have hl1 := Util.readLE8_lt s.mem 5980584
  have hl2 := Util.readLE8_lt s.mem 5980592
  have hl3 := Util.readLE8_lt s.mem 5980600
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980576 12919594847110692864 54210108624275221 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980584 8 = 54210108624275221 := hT1'
  have hT2 : s.mem.readLE 5980592 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980600 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980576 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 12919594847110692864 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980576 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980584 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210108624275221 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980584 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980592 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980592 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980600 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980600 8) = T3 := fun v => by
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
theorem c1_56 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 55 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 56)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 8 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 56 := Util.bitLen_of_range _ 56 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980576 32 = 1000000000000000000000000000000000000 := by simpa using hTB.2 16 (by decide)
  have hTa : s.mem.accessible 5980576 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980576
  have hl1 := Util.readLE8_lt s.mem 5980584
  have hl2 := Util.readLE8_lt s.mem 5980592
  have hl3 := Util.readLE8_lt s.mem 5980600
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980576 12919594847110692864 54210108624275221 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980584 8 = 54210108624275221 := hT1'
  have hT2 : s.mem.readLE 5980592 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980600 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980576 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 12919594847110692864 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980576 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980584 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210108624275221 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980584 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980592 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980592 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980600 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980600 8) = T3 := fun v => by
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
theorem c1_57 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 56 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 57)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 7 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 57 := Util.bitLen_of_range _ 57 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980576 32 = 1000000000000000000000000000000000000 := by simpa using hTB.2 16 (by decide)
  have hTa : s.mem.accessible 5980576 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980576
  have hl1 := Util.readLE8_lt s.mem 5980584
  have hl2 := Util.readLE8_lt s.mem 5980592
  have hl3 := Util.readLE8_lt s.mem 5980600
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980576 12919594847110692864 54210108624275221 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980584 8 = 54210108624275221 := hT1'
  have hT2 : s.mem.readLE 5980592 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980600 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980576 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 12919594847110692864 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980576 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980584 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 54210108624275221 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980584 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980592 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980592 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980600 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980600 8) = T3 := fun v => by
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
theorem c1_58 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 57 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 58)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 6 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 58 := Util.bitLen_of_range _ 58 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980608 32 = 10000000000000000000000000000000000000 := by simpa using hTB.2 17 (by decide)
  have hTa : s.mem.accessible 5980608 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980608
  have hl1 := Util.readLE8_lt s.mem 5980616
  have hl2 := Util.readLE8_lt s.mem 5980624
  have hl3 := Util.readLE8_lt s.mem 5980632
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980608 68739955140067328 542101086242752217 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980616 8 = 542101086242752217 := hT1'
  have hT2 : s.mem.readLE 5980624 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980632 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980608 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 68739955140067328 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980608 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980616 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101086242752217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980616 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980624 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980624 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980632 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980632 8) = T3 := fun v => by
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
theorem c1_59 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 58 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 59)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 5 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 59 := Util.bitLen_of_range _ 59 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980608 32 = 10000000000000000000000000000000000000 := by simpa using hTB.2 17 (by decide)
  have hTa : s.mem.accessible 5980608 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980608
  have hl1 := Util.readLE8_lt s.mem 5980616
  have hl2 := Util.readLE8_lt s.mem 5980624
  have hl3 := Util.readLE8_lt s.mem 5980632
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980608 68739955140067328 542101086242752217 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980616 8 = 542101086242752217 := hT1'
  have hT2 : s.mem.readLE 5980624 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980632 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980608 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 68739955140067328 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980608 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980616 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101086242752217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980616 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980624 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980624 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980632 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980632 8) = T3 := fun v => by
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
theorem c1_60 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 59 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 60)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 4 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 60 := Util.bitLen_of_range _ 60 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980608 32 = 10000000000000000000000000000000000000 := by simpa using hTB.2 17 (by decide)
  have hTa : s.mem.accessible 5980608 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980608
  have hl1 := Util.readLE8_lt s.mem 5980616
  have hl2 := Util.readLE8_lt s.mem 5980624
  have hl3 := Util.readLE8_lt s.mem 5980632
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980608 68739955140067328 542101086242752217 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980616 8 = 542101086242752217 := hT1'
  have hT2 : s.mem.readLE 5980624 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980632 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980608 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 68739955140067328 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980608 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980616 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101086242752217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980616 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980624 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980624 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980632 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980632 8) = T3 := fun v => by
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
theorem c1_61 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 60 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 61)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 3 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 61 := Util.bitLen_of_range _ 61 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980608 32 = 10000000000000000000000000000000000000 := by simpa using hTB.2 17 (by decide)
  have hTa : s.mem.accessible 5980608 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980608
  have hl1 := Util.readLE8_lt s.mem 5980616
  have hl2 := Util.readLE8_lt s.mem 5980624
  have hl3 := Util.readLE8_lt s.mem 5980632
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980608 68739955140067328 542101086242752217 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980616 8 = 542101086242752217 := hT1'
  have hT2 : s.mem.readLE 5980624 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980632 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980608 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 68739955140067328 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980608 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980616 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 542101086242752217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980616 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980624 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980624 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980632 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980632 8) = T3 := fun v => by
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
theorem c1_62 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 61 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 62)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 2 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 62 := Util.bitLen_of_range _ 62 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980640 32 = 100000000000000000000000000000000000000 := by simpa using hTB.2 18 (by decide)
  have hTa : s.mem.accessible 5980640 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980640
  have hl1 := Util.readLE8_lt s.mem 5980648
  have hl2 := Util.readLE8_lt s.mem 5980656
  have hl3 := Util.readLE8_lt s.mem 5980664
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980640 687399551400673280 5421010862427522170 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980648 8 = 5421010862427522170 := hT1'
  have hT2 : s.mem.readLE 5980656 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980664 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980640 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 687399551400673280 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980640 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980648 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421010862427522170 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980648 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980656 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980656 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980664 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980664 8) = T3 := fun v => by
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
theorem c1_63 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 62 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 63)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 1 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 63 := Util.bitLen_of_range _ 63 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980640 32 = 100000000000000000000000000000000000000 := by simpa using hTB.2 18 (by decide)
  have hTa : s.mem.accessible 5980640 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980640
  have hl1 := Util.readLE8_lt s.mem 5980648
  have hl2 := Util.readLE8_lt s.mem 5980656
  have hl3 := Util.readLE8_lt s.mem 5980664
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980640 687399551400673280 5421010862427522170 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980648 8 = 5421010862427522170 := hT1'
  have hT2 : s.mem.readLE 5980656 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980664 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980640 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 687399551400673280 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980640 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980648 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421010862427522170 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980648 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980656 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980656 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980664 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980664 8) = T3 := fun v => by
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
theorem c1_64 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 63 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 64)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 0 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 64 := Util.bitLen_of_range _ 64 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980640 32 = 100000000000000000000000000000000000000 := by simpa using hTB.2 18 (by decide)
  have hTa : s.mem.accessible 5980640 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980640
  have hl1 := Util.readLE8_lt s.mem 5980648
  have hl2 := Util.readLE8_lt s.mem 5980656
  have hl3 := Util.readLE8_lt s.mem 5980664
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980640 687399551400673280 5421010862427522170 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980648 8 = 5421010862427522170 := hT1'
  have hT2 : s.mem.readLE 5980656 8 = 0 := hT2'
  have hT3 : s.mem.readLE 5980664 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980640 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 687399551400673280 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980640 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980648 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5421010862427522170 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980648 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980656 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 0 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980656 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980664 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980664 8) = T3 := fun v => by
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
theorem c2_1 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 0 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 1)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 63 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 1 := Util.bitLen_of_range _ 1 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980672 32 = 1000000000000000000000000000000000000000 := by simpa using hTB.2 19 (by decide)
  have hTa : s.mem.accessible 5980672 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980672
  have hl1 := Util.readLE8_lt s.mem 5980680
  have hl2 := Util.readLE8_lt s.mem 5980688
  have hl3 := Util.readLE8_lt s.mem 5980696
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980672 6873995514006732800 17316620476856118468 2 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980680 8 = 17316620476856118468 := hT1'
  have hT2 : s.mem.readLE 5980688 8 = 2 := hT2'
  have hT3 : s.mem.readLE 5980696 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980672 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6873995514006732800 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980672 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980680 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17316620476856118468 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980680 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980688 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980688 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980696 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980696 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_2 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 1 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 2)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 62 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 2 := Util.bitLen_of_range _ 2 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980672 32 = 1000000000000000000000000000000000000000 := by simpa using hTB.2 19 (by decide)
  have hTa : s.mem.accessible 5980672 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980672
  have hl1 := Util.readLE8_lt s.mem 5980680
  have hl2 := Util.readLE8_lt s.mem 5980688
  have hl3 := Util.readLE8_lt s.mem 5980696
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980672 6873995514006732800 17316620476856118468 2 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980680 8 = 17316620476856118468 := hT1'
  have hT2 : s.mem.readLE 5980688 8 = 2 := hT2'
  have hT3 : s.mem.readLE 5980696 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980672 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6873995514006732800 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980672 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980680 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17316620476856118468 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980680 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980688 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980688 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980696 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980696 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_3 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 2 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 3)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 61 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 3 := Util.bitLen_of_range _ 3 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980672 32 = 1000000000000000000000000000000000000000 := by simpa using hTB.2 19 (by decide)
  have hTa : s.mem.accessible 5980672 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980672
  have hl1 := Util.readLE8_lt s.mem 5980680
  have hl2 := Util.readLE8_lt s.mem 5980688
  have hl3 := Util.readLE8_lt s.mem 5980696
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980672 6873995514006732800 17316620476856118468 2 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980680 8 = 17316620476856118468 := hT1'
  have hT2 : s.mem.readLE 5980688 8 = 2 := hT2'
  have hT3 : s.mem.readLE 5980696 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980672 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6873995514006732800 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980672 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980680 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17316620476856118468 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980680 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980688 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980688 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980696 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980696 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_4 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 3 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 4)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 60 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 4 := Util.bitLen_of_range _ 4 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980704 32 = 10000000000000000000000000000000000000000 := by simpa using hTB.2 20 (by decide)
  have hTa : s.mem.accessible 5980704 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980704
  have hl1 := Util.readLE8_lt s.mem 5980712
  have hl2 := Util.readLE8_lt s.mem 5980720
  have hl3 := Util.readLE8_lt s.mem 5980728
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980704 13399722918938673152 7145508105175220139 29 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980712 8 = 7145508105175220139 := hT1'
  have hT2 : s.mem.readLE 5980720 8 = 29 := hT2'
  have hT3 : s.mem.readLE 5980728 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980704 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13399722918938673152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980704 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980712 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7145508105175220139 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980712 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980720 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980720 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980728 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980728 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_5 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 4 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 5)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 59 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 5 := Util.bitLen_of_range _ 5 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980704 32 = 10000000000000000000000000000000000000000 := by simpa using hTB.2 20 (by decide)
  have hTa : s.mem.accessible 5980704 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980704
  have hl1 := Util.readLE8_lt s.mem 5980712
  have hl2 := Util.readLE8_lt s.mem 5980720
  have hl3 := Util.readLE8_lt s.mem 5980728
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980704 13399722918938673152 7145508105175220139 29 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980712 8 = 7145508105175220139 := hT1'
  have hT2 : s.mem.readLE 5980720 8 = 29 := hT2'
  have hT3 : s.mem.readLE 5980728 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980704 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13399722918938673152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980704 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980712 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7145508105175220139 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980712 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980720 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980720 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980728 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980728 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_6 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 5 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 6)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 58 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 6 := Util.bitLen_of_range _ 6 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980704 32 = 10000000000000000000000000000000000000000 := by simpa using hTB.2 20 (by decide)
  have hTa : s.mem.accessible 5980704 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980704
  have hl1 := Util.readLE8_lt s.mem 5980712
  have hl2 := Util.readLE8_lt s.mem 5980720
  have hl3 := Util.readLE8_lt s.mem 5980728
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980704 13399722918938673152 7145508105175220139 29 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980712 8 = 7145508105175220139 := hT1'
  have hT2 : s.mem.readLE 5980720 8 = 29 := hT2'
  have hT3 : s.mem.readLE 5980728 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980704 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13399722918938673152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980704 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980712 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7145508105175220139 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980712 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980720 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980720 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980728 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980728 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c2_7 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 6 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 7)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 57 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 7 := Util.bitLen_of_range _ 7 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980704 32 = 10000000000000000000000000000000000000000 := by simpa using hTB.2 20 (by decide)
  have hTa : s.mem.accessible 5980704 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980704
  have hl1 := Util.readLE8_lt s.mem 5980712
  have hl2 := Util.readLE8_lt s.mem 5980720
  have hl3 := Util.readLE8_lt s.mem 5980728
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980704 13399722918938673152 7145508105175220139 29 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980712 8 = 7145508105175220139 := hT1'
  have hT2 : s.mem.readLE 5980720 8 = 29 := hT2'
  have hT3 : s.mem.readLE 5980728 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980704 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13399722918938673152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980704 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980712 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7145508105175220139 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980712 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980720 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980720 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980728 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980728 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 16) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hz3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

end Fv256.Amd64.Log10
