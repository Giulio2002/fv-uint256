import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c2_25 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 24 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 25)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 39 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 25 := Util.bitLen_of_range _ 25 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980896 32 = 10000000000000000000000000000000000000000000000 := by simpa using hTB.2 26 (by decide)
  have hTa : s.mem.accessible 5980896 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980896
  have hl1 := Util.readLE8_lt s.mem 5980904
  have hl2 := Util.readLE8_lt s.mem 5980912
  have hl3 := Util.readLE8_lt s.mem 5980920
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980896 8023796054858137600 14214271235644855872 29387358 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980904 8 = 14214271235644855872 := hT1'
  have hT2 : s.mem.readLE 5980912 8 = 29387358 := hT2'
  have hT3 : s.mem.readLE 5980920 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980896 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 8023796054858137600 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980896 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980904 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 14214271235644855872 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980904 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980912 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980912 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980920 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980920 8) = T3 := fun v => by
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
theorem c2_26 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 25 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 26)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 38 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 26 := Util.bitLen_of_range _ 26 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980896 32 = 10000000000000000000000000000000000000000000000 := by simpa using hTB.2 26 (by decide)
  have hTa : s.mem.accessible 5980896 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980896
  have hl1 := Util.readLE8_lt s.mem 5980904
  have hl2 := Util.readLE8_lt s.mem 5980912
  have hl3 := Util.readLE8_lt s.mem 5980920
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980896 8023796054858137600 14214271235644855872 29387358 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980904 8 = 14214271235644855872 := hT1'
  have hT2 : s.mem.readLE 5980912 8 = 29387358 := hT2'
  have hT3 : s.mem.readLE 5980920 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980896 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 8023796054858137600 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980896 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980904 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 14214271235644855872 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980904 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980912 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980912 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980920 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980920 8) = T3 := fun v => by
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
theorem c2_27 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 26 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 27)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 37 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 27 := Util.bitLen_of_range _ 27 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980896 32 = 10000000000000000000000000000000000000000000000 := by simpa using hTB.2 26 (by decide)
  have hTa : s.mem.accessible 5980896 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980896
  have hl1 := Util.readLE8_lt s.mem 5980904
  have hl2 := Util.readLE8_lt s.mem 5980912
  have hl3 := Util.readLE8_lt s.mem 5980920
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980896 8023796054858137600 14214271235644855872 29387358 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980904 8 = 14214271235644855872 := hT1'
  have hT2 : s.mem.readLE 5980912 8 = 29387358 := hT2'
  have hT3 : s.mem.readLE 5980920 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980896 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 8023796054858137600 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980896 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980904 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 14214271235644855872 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980904 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980912 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980912 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980920 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980920 8) = T3 := fun v => by
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
theorem c2_28 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 27 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 28)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 36 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 28 := Util.bitLen_of_range _ 28 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980928 32 = 100000000000000000000000000000000000000000000000 := by simpa using hTB.2 27 (by decide)
  have hTa : s.mem.accessible 5980928 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980928
  have hl1 := Util.readLE8_lt s.mem 5980936
  have hl2 := Util.readLE8_lt s.mem 5980944
  have hl3 := Util.readLE8_lt s.mem 5980952
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980928 6450984253743169536 13015503840481697412 293873587 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980936 8 = 13015503840481697412 := hT1'
  have hT2 : s.mem.readLE 5980944 8 = 293873587 := hT2'
  have hT3 : s.mem.readLE 5980952 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980928 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6450984253743169536 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980928 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980936 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 13015503840481697412 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980936 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980944 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980944 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980952 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980952 8) = T3 := fun v => by
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
theorem c2_29 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 28 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 29)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 35 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 29 := Util.bitLen_of_range _ 29 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980928 32 = 100000000000000000000000000000000000000000000000 := by simpa using hTB.2 27 (by decide)
  have hTa : s.mem.accessible 5980928 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980928
  have hl1 := Util.readLE8_lt s.mem 5980936
  have hl2 := Util.readLE8_lt s.mem 5980944
  have hl3 := Util.readLE8_lt s.mem 5980952
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980928 6450984253743169536 13015503840481697412 293873587 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980936 8 = 13015503840481697412 := hT1'
  have hT2 : s.mem.readLE 5980944 8 = 293873587 := hT2'
  have hT3 : s.mem.readLE 5980952 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980928 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6450984253743169536 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980928 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980936 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 13015503840481697412 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980936 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980944 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980944 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980952 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980952 8) = T3 := fun v => by
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
theorem c2_30 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 29 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 30)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 34 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 30 := Util.bitLen_of_range _ 30 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980928 32 = 100000000000000000000000000000000000000000000000 := by simpa using hTB.2 27 (by decide)
  have hTa : s.mem.accessible 5980928 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980928
  have hl1 := Util.readLE8_lt s.mem 5980936
  have hl2 := Util.readLE8_lt s.mem 5980944
  have hl3 := Util.readLE8_lt s.mem 5980952
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980928 6450984253743169536 13015503840481697412 293873587 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980936 8 = 13015503840481697412 := hT1'
  have hT2 : s.mem.readLE 5980944 8 = 293873587 := hT2'
  have hT3 : s.mem.readLE 5980952 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980928 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 6450984253743169536 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980928 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980936 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 13015503840481697412 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980936 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980944 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980944 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980952 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980952 8) = T3 := fun v => by
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
theorem c2_31 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 30 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 31)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 33 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 31 := Util.bitLen_of_range _ 31 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980960 32 = 1000000000000000000000000000000000000000000000000 := by simpa using hTB.2 28 (by decide)
  have hTa : s.mem.accessible 5980960 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980960
  have hl1 := Util.readLE8_lt s.mem 5980968
  have hl2 := Util.readLE8_lt s.mem 5980976
  have hl3 := Util.readLE8_lt s.mem 5980984
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980960 9169610316303040512 1027829888850112811 2938735877 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980968 8 = 1027829888850112811 := hT1'
  have hT2 : s.mem.readLE 5980976 8 = 2938735877 := hT2'
  have hT3 : s.mem.readLE 5980984 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980960 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9169610316303040512 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980960 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980968 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 1027829888850112811 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980968 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980976 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980976 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980984 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980984 8) = T3 := fun v => by
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
theorem c2_32 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 31 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 32)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 32 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 32 := Util.bitLen_of_range _ 32 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980960 32 = 1000000000000000000000000000000000000000000000000 := by simpa using hTB.2 28 (by decide)
  have hTa : s.mem.accessible 5980960 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980960
  have hl1 := Util.readLE8_lt s.mem 5980968
  have hl2 := Util.readLE8_lt s.mem 5980976
  have hl3 := Util.readLE8_lt s.mem 5980984
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980960 9169610316303040512 1027829888850112811 2938735877 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980968 8 = 1027829888850112811 := hT1'
  have hT2 : s.mem.readLE 5980976 8 = 2938735877 := hT2'
  have hT3 : s.mem.readLE 5980984 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980960 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9169610316303040512 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980960 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980968 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 1027829888850112811 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980968 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980976 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980976 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980984 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980984 8) = T3 := fun v => by
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
theorem c2_33 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 32 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 33)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 31 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 33 := Util.bitLen_of_range _ 33 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980960 32 = 1000000000000000000000000000000000000000000000000 := by simpa using hTB.2 28 (by decide)
  have hTa : s.mem.accessible 5980960 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980960
  have hl1 := Util.readLE8_lt s.mem 5980968
  have hl2 := Util.readLE8_lt s.mem 5980976
  have hl3 := Util.readLE8_lt s.mem 5980984
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980960 9169610316303040512 1027829888850112811 2938735877 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5980968 8 = 1027829888850112811 := hT1'
  have hT2 : s.mem.readLE 5980976 8 = 2938735877 := hT2'
  have hT3 : s.mem.readLE 5980984 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980960 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9169610316303040512 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980960 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5980968 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 1027829888850112811 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980968 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5980976 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980976 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5980984 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980984 8) = T3 := fun v => by
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
theorem c2_34 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 33 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 34)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 30 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 34 := Util.bitLen_of_range _ 34 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980992 32 = 10000000000000000000000000000000000000000000000000 := by simpa using hTB.2 29 (by decide)
  have hTa : s.mem.accessible 5980992 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980992
  have hl1 := Util.readLE8_lt s.mem 5981000
  have hl2 := Util.readLE8_lt s.mem 5981008
  have hl3 := Util.readLE8_lt s.mem 5981016
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980992 17909126868192198656 10278298888501128114 29387358770 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981000 8 = 10278298888501128114 := hT1'
  have hT2 : s.mem.readLE 5981008 8 = 29387358770 := hT2'
  have hT3 : s.mem.readLE 5981016 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980992 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 17909126868192198656 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980992 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981000 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10278298888501128114 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981000 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981008 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358770 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981008 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981016 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981016 8) = T3 := fun v => by
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
theorem c2_35 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 34 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 35)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 29 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 35 := Util.bitLen_of_range _ 35 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980992 32 = 10000000000000000000000000000000000000000000000000 := by simpa using hTB.2 29 (by decide)
  have hTa : s.mem.accessible 5980992 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980992
  have hl1 := Util.readLE8_lt s.mem 5981000
  have hl2 := Util.readLE8_lt s.mem 5981008
  have hl3 := Util.readLE8_lt s.mem 5981016
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980992 17909126868192198656 10278298888501128114 29387358770 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981000 8 = 10278298888501128114 := hT1'
  have hT2 : s.mem.readLE 5981008 8 = 29387358770 := hT2'
  have hT3 : s.mem.readLE 5981016 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980992 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 17909126868192198656 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980992 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981000 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10278298888501128114 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981000 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981008 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358770 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981008 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981016 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981016 8) = T3 := fun v => by
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
theorem c2_36 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 35 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 36)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 28 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 36 := Util.bitLen_of_range _ 36 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980992 32 = 10000000000000000000000000000000000000000000000000 := by simpa using hTB.2 29 (by decide)
  have hTa : s.mem.accessible 5980992 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980992
  have hl1 := Util.readLE8_lt s.mem 5981000
  have hl2 := Util.readLE8_lt s.mem 5981008
  have hl3 := Util.readLE8_lt s.mem 5981016
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980992 17909126868192198656 10278298888501128114 29387358770 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981000 8 = 10278298888501128114 := hT1'
  have hT2 : s.mem.readLE 5981008 8 = 29387358770 := hT2'
  have hT3 : s.mem.readLE 5981016 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980992 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 17909126868192198656 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980992 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981000 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10278298888501128114 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981000 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981008 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358770 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981008 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981016 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981016 8) = T3 := fun v => by
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
theorem c2_37 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 36 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 37)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 27 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 37 := Util.bitLen_of_range _ 37 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5980992 32 = 10000000000000000000000000000000000000000000000000 := by simpa using hTB.2 29 (by decide)
  have hTa : s.mem.accessible 5980992 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5980992
  have hl1 := Util.readLE8_lt s.mem 5981000
  have hl2 := Util.readLE8_lt s.mem 5981008
  have hl3 := Util.readLE8_lt s.mem 5981016
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5980992 17909126868192198656 10278298888501128114 29387358770 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981000 8 = 10278298888501128114 := hT1'
  have hT2 : s.mem.readLE 5981008 8 = 29387358770 := hT2'
  have hT3 : s.mem.readLE 5981016 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5980992 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 17909126868192198656 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5980992 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981000 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10278298888501128114 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981000 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981008 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 29387358770 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981008 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981016 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981016 8) = T3 := fun v => by
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
theorem c2_38 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 37 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 38)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 26 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 38 := Util.bitLen_of_range _ 38 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981024 32 = 100000000000000000000000000000000000000000000000000 := by simpa using hTB.2 30 (by decide)
  have hTa : s.mem.accessible 5981024 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981024
  have hl1 := Util.readLE8_lt s.mem 5981032
  have hl2 := Util.readLE8_lt s.mem 5981040
  have hl3 := Util.readLE8_lt s.mem 5981048
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981024 13070572018536022016 10549268516463523069 293873587705 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981032 8 = 10549268516463523069 := hT1'
  have hT2 : s.mem.readLE 5981040 8 = 293873587705 := hT2'
  have hT3 : s.mem.readLE 5981048 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981024 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13070572018536022016 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981024 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981032 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10549268516463523069 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981032 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981040 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587705 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981040 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981048 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981048 8) = T3 := fun v => by
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
theorem c2_39 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 38 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 39)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 25 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 39 := Util.bitLen_of_range _ 39 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981024 32 = 100000000000000000000000000000000000000000000000000 := by simpa using hTB.2 30 (by decide)
  have hTa : s.mem.accessible 5981024 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981024
  have hl1 := Util.readLE8_lt s.mem 5981032
  have hl2 := Util.readLE8_lt s.mem 5981040
  have hl3 := Util.readLE8_lt s.mem 5981048
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981024 13070572018536022016 10549268516463523069 293873587705 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981032 8 = 10549268516463523069 := hT1'
  have hT2 : s.mem.readLE 5981040 8 = 293873587705 := hT2'
  have hT3 : s.mem.readLE 5981048 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981024 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13070572018536022016 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981024 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981032 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10549268516463523069 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981032 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981040 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587705 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981040 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981048 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981048 8) = T3 := fun v => by
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
theorem c2_40 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 39 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 40)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 24 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 40 := Util.bitLen_of_range _ 40 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981024 32 = 100000000000000000000000000000000000000000000000000 := by simpa using hTB.2 30 (by decide)
  have hTa : s.mem.accessible 5981024 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981024
  have hl1 := Util.readLE8_lt s.mem 5981032
  have hl2 := Util.readLE8_lt s.mem 5981040
  have hl3 := Util.readLE8_lt s.mem 5981048
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981024 13070572018536022016 10549268516463523069 293873587705 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981032 8 = 10549268516463523069 := hT1'
  have hT2 : s.mem.readLE 5981040 8 = 293873587705 := hT2'
  have hT3 : s.mem.readLE 5981048 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981024 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 13070572018536022016 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981024 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981032 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 10549268516463523069 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981032 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981040 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587705 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981040 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981048 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981048 8) = T3 := fun v => by
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
theorem c2_41 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 40 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 41)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 23 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 41 := Util.bitLen_of_range _ 41 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981056 32 = 1000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 31 (by decide)
  have hTa : s.mem.accessible 5981056 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981056
  have hl1 := Util.readLE8_lt s.mem 5981064
  have hl2 := Util.readLE8_lt s.mem 5981072
  have hl3 := Util.readLE8_lt s.mem 5981080
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981056 1578511669393358848 13258964796087472617 2938735877055 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981064 8 = 13258964796087472617 := hT1'
  have hT2 : s.mem.readLE 5981072 8 = 2938735877055 := hT2'
  have hT3 : s.mem.readLE 5981080 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981056 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1578511669393358848 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981056 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981064 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 13258964796087472617 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981064 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981072 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877055 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981072 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981080 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981080 8) = T3 := fun v => by
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
