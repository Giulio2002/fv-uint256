import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c3_12 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 11 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 12)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 52 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 12 := Util.bitLen_of_range _ 12 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981376 32 = 10000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 41 (by decide)
  have hTa : s.mem.accessible 5981376 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981376
  have hl1 := Util.readLE8_lt s.mem 5981384
  have hl2 := Util.readLE8_lt s.mem 5981392
  have hl3 := Util.readLE8_lt s.mem 5981400
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981376 11529215046068469760 7626447661401876602 1695461137871974930 1593 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981384 8 = 7626447661401876602 := hT1'
  have hT2 : s.mem.readLE 5981392 8 = 1695461137871974930 := hT2'
  have hT3 : s.mem.readLE 5981400 8 = 1593 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981376 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 11529215046068469760 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981376 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981384 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7626447661401876602 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981384 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981392 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 1695461137871974930 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981392 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981400 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1593 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981400 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_13 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 12 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 13)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 51 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 13 := Util.bitLen_of_range _ 13 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981408 32 = 100000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 42 (by decide)
  have hTa : s.mem.accessible 5981408 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981408
  have hl1 := Util.readLE8_lt s.mem 5981416
  have hl2 := Util.readLE8_lt s.mem 5981424
  have hl3 := Util.readLE8_lt s.mem 5981432
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981408 4611686018427387904 2477500319180559562 16954611378719749304 15930 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981416 8 = 2477500319180559562 := hT1'
  have hT2 : s.mem.readLE 5981424 8 = 16954611378719749304 := hT2'
  have hT3 : s.mem.readLE 5981432 8 = 15930 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981408 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 4611686018427387904 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981408 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981416 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 2477500319180559562 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981416 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981424 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16954611378719749304 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981424 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981432 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981432 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_14 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 13 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 14)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 50 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 14 := Util.bitLen_of_range _ 14 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981408 32 = 100000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 42 (by decide)
  have hTa : s.mem.accessible 5981408 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981408
  have hl1 := Util.readLE8_lt s.mem 5981416
  have hl2 := Util.readLE8_lt s.mem 5981424
  have hl3 := Util.readLE8_lt s.mem 5981432
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981408 4611686018427387904 2477500319180559562 16954611378719749304 15930 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981416 8 = 2477500319180559562 := hT1'
  have hT2 : s.mem.readLE 5981424 8 = 16954611378719749304 := hT2'
  have hT3 : s.mem.readLE 5981432 8 = 15930 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981408 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 4611686018427387904 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981408 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981416 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 2477500319180559562 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981416 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981424 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16954611378719749304 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981424 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981432 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981432 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_15 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 14 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 15)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 49 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 15 := Util.bitLen_of_range _ 15 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981408 32 = 100000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 42 (by decide)
  have hTa : s.mem.accessible 5981408 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981408
  have hl1 := Util.readLE8_lt s.mem 5981416
  have hl2 := Util.readLE8_lt s.mem 5981424
  have hl3 := Util.readLE8_lt s.mem 5981432
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981408 4611686018427387904 2477500319180559562 16954611378719749304 15930 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981416 8 = 2477500319180559562 := hT1'
  have hT2 : s.mem.readLE 5981424 8 = 16954611378719749304 := hT2'
  have hT3 : s.mem.readLE 5981432 8 = 15930 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981408 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 4611686018427387904 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981408 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981416 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 2477500319180559562 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981416 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981424 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16954611378719749304 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981424 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981432 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981432 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_16 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 15 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 16)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 48 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 16 := Util.bitLen_of_range _ 16 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981408 32 = 100000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 42 (by decide)
  have hTa : s.mem.accessible 5981408 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981408
  have hl1 := Util.readLE8_lt s.mem 5981416
  have hl2 := Util.readLE8_lt s.mem 5981424
  have hl3 := Util.readLE8_lt s.mem 5981432
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981408 4611686018427387904 2477500319180559562 16954611378719749304 15930 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981416 8 = 2477500319180559562 := hT1'
  have hT2 : s.mem.readLE 5981424 8 = 16954611378719749304 := hT2'
  have hT3 : s.mem.readLE 5981432 8 = 15930 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981408 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 4611686018427387904 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981408 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981416 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 2477500319180559562 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981416 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981424 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16954611378719749304 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981424 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981432 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981432 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_17 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 16 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 17)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 47 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 17 := Util.bitLen_of_range _ 17 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981440 32 = 1000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 43 (by decide)
  have hTa : s.mem.accessible 5981440 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981440
  have hl1 := Util.readLE8_lt s.mem 5981448
  have hl2 := Util.readLE8_lt s.mem 5981456
  have hl3 := Util.readLE8_lt s.mem 5981464
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981440 9223372036854775808 6328259118096044006 3525417123811528497 159309 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981448 8 = 6328259118096044006 := hT1'
  have hT2 : s.mem.readLE 5981456 8 = 3525417123811528497 := hT2'
  have hT3 : s.mem.readLE 5981464 8 = 159309 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981440 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9223372036854775808 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981440 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981448 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 6328259118096044006 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981448 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981456 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 3525417123811528497 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981456 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981464 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159309 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981464 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_18 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 17 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 18)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 46 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 18 := Util.bitLen_of_range _ 18 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981440 32 = 1000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 43 (by decide)
  have hTa : s.mem.accessible 5981440 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981440
  have hl1 := Util.readLE8_lt s.mem 5981448
  have hl2 := Util.readLE8_lt s.mem 5981456
  have hl3 := Util.readLE8_lt s.mem 5981464
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981440 9223372036854775808 6328259118096044006 3525417123811528497 159309 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981448 8 = 6328259118096044006 := hT1'
  have hT2 : s.mem.readLE 5981456 8 = 3525417123811528497 := hT2'
  have hT3 : s.mem.readLE 5981464 8 = 159309 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981440 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9223372036854775808 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981440 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981448 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 6328259118096044006 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981448 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981456 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 3525417123811528497 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981456 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981464 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159309 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981464 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_19 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 18 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 19)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 45 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 19 := Util.bitLen_of_range _ 19 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981440 32 = 1000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 43 (by decide)
  have hTa : s.mem.accessible 5981440 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981440
  have hl1 := Util.readLE8_lt s.mem 5981448
  have hl2 := Util.readLE8_lt s.mem 5981456
  have hl3 := Util.readLE8_lt s.mem 5981464
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981440 9223372036854775808 6328259118096044006 3525417123811528497 159309 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981448 8 = 6328259118096044006 := hT1'
  have hT2 : s.mem.readLE 5981456 8 = 3525417123811528497 := hT2'
  have hT3 : s.mem.readLE 5981464 8 = 159309 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981440 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 9223372036854775808 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981440 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981448 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 6328259118096044006 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981448 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981456 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 3525417123811528497 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981456 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981464 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159309 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981464 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_20 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 19 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 20)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 44 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 20 := Util.bitLen_of_range _ 20 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981472 32 = 10000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 44 (by decide)
  have hTa : s.mem.accessible 5981472 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981472
  have hl1 := Util.readLE8_lt s.mem 5981480
  have hl2 := Util.readLE8_lt s.mem 5981488
  have hl3 := Util.readLE8_lt s.mem 5981496
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981472 0 7942358959831785217 16807427164405733357 1593091 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981480 8 = 7942358959831785217 := hT1'
  have hT2 : s.mem.readLE 5981488 8 = 16807427164405733357 := hT2'
  have hT3 : s.mem.readLE 5981496 8 = 1593091 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981472 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981472 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981480 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7942358959831785217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981480 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981488 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16807427164405733357 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981488 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981496 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1593091 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981496 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_21 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 20 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 21)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 43 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 21 := Util.bitLen_of_range _ 21 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981472 32 = 10000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 44 (by decide)
  have hTa : s.mem.accessible 5981472 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981472
  have hl1 := Util.readLE8_lt s.mem 5981480
  have hl2 := Util.readLE8_lt s.mem 5981488
  have hl3 := Util.readLE8_lt s.mem 5981496
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981472 0 7942358959831785217 16807427164405733357 1593091 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981480 8 = 7942358959831785217 := hT1'
  have hT2 : s.mem.readLE 5981488 8 = 16807427164405733357 := hT2'
  have hT3 : s.mem.readLE 5981496 8 = 1593091 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981472 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981472 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981480 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7942358959831785217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981480 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981488 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16807427164405733357 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981488 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981496 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1593091 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981496 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_22 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 21 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 22)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 42 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 22 := Util.bitLen_of_range _ 22 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981472 32 = 10000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 44 (by decide)
  have hTa : s.mem.accessible 5981472 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981472
  have hl1 := Util.readLE8_lt s.mem 5981480
  have hl2 := Util.readLE8_lt s.mem 5981488
  have hl3 := Util.readLE8_lt s.mem 5981496
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981472 0 7942358959831785217 16807427164405733357 1593091 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981480 8 = 7942358959831785217 := hT1'
  have hT2 : s.mem.readLE 5981488 8 = 16807427164405733357 := hT2'
  have hT3 : s.mem.readLE 5981496 8 = 1593091 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981472 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981472 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981480 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 7942358959831785217 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981480 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981488 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 16807427164405733357 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981488 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981496 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1593091 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981496 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_23 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 22 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 23)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 41 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 23 := Util.bitLen_of_range _ 23 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981504 32 = 100000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 45 (by decide)
  have hTa : s.mem.accessible 5981504 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981504
  have hl1 := Util.readLE8_lt s.mem 5981512
  have hl2 := Util.readLE8_lt s.mem 5981520
  have hl3 := Util.readLE8_lt s.mem 5981528
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981504 0 5636613303479645706 2053574980671369030 15930919 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981512 8 = 5636613303479645706 := hT1'
  have hT2 : s.mem.readLE 5981520 8 = 2053574980671369030 := hT2'
  have hT3 : s.mem.readLE 5981528 8 = 15930919 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981504 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981504 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981512 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5636613303479645706 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981512 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981520 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2053574980671369030 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981520 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981528 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930919 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981528 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_24 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 23 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 24)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 40 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 24 := Util.bitLen_of_range _ 24 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981504 32 = 100000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 45 (by decide)
  have hTa : s.mem.accessible 5981504 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981504
  have hl1 := Util.readLE8_lt s.mem 5981512
  have hl2 := Util.readLE8_lt s.mem 5981520
  have hl3 := Util.readLE8_lt s.mem 5981528
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981504 0 5636613303479645706 2053574980671369030 15930919 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981512 8 = 5636613303479645706 := hT1'
  have hT2 : s.mem.readLE 5981520 8 = 2053574980671369030 := hT2'
  have hT3 : s.mem.readLE 5981528 8 = 15930919 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981504 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981504 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981512 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5636613303479645706 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981512 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981520 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2053574980671369030 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981520 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981528 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930919 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981528 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_25 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 24 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 25)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 39 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 25 := Util.bitLen_of_range _ 25 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981504 32 = 100000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 45 (by decide)
  have hTa : s.mem.accessible 5981504 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981504
  have hl1 := Util.readLE8_lt s.mem 5981512
  have hl2 := Util.readLE8_lt s.mem 5981520
  have hl3 := Util.readLE8_lt s.mem 5981528
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981504 0 5636613303479645706 2053574980671369030 15930919 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981512 8 = 5636613303479645706 := hT1'
  have hT2 : s.mem.readLE 5981520 8 = 2053574980671369030 := hT2'
  have hT3 : s.mem.readLE 5981528 8 = 15930919 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981504 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981504 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981512 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5636613303479645706 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981512 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981520 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2053574980671369030 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981520 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981528 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930919 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981528 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_26 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 25 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 26)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 38 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 26 := Util.bitLen_of_range _ 26 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981504 32 = 100000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 45 (by decide)
  have hTa : s.mem.accessible 5981504 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981504
  have hl1 := Util.readLE8_lt s.mem 5981512
  have hl2 := Util.readLE8_lt s.mem 5981520
  have hl3 := Util.readLE8_lt s.mem 5981528
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981504 0 5636613303479645706 2053574980671369030 15930919 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981512 8 = 5636613303479645706 := hT1'
  have hT2 : s.mem.readLE 5981520 8 = 2053574980671369030 := hT2'
  have hT3 : s.mem.readLE 5981528 8 = 15930919 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981504 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981504 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981512 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 5636613303479645706 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981512 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981520 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2053574980671369030 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981520 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981528 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15930919 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981528 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_27 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 26 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 27)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 37 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 27 := Util.bitLen_of_range _ 27 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981536 32 = 1000000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 46 (by decide)
  have hTa : s.mem.accessible 5981536 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981536
  have hl1 := Util.readLE8_lt s.mem 5981544
  have hl2 := Util.readLE8_lt s.mem 5981552
  have hl3 := Util.readLE8_lt s.mem 5981560
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981536 0 1025900813667802212 2089005733004138687 159309191 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981544 8 = 1025900813667802212 := hT1'
  have hT2 : s.mem.readLE 5981552 8 = 2089005733004138687 := hT2'
  have hT3 : s.mem.readLE 5981560 8 = 159309191 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981536 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981536 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981544 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 1025900813667802212 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981544 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981552 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2089005733004138687 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981552 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981560 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159309191 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981560 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

set_option maxHeartbeats 64000000 in
theorem c3_28 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 27 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 28)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 36 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 28 := Util.bitLen_of_range _ 28 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981536 32 = 1000000000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 46 (by decide)
  have hTa : s.mem.accessible 5981536 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981536
  have hl1 := Util.readLE8_lt s.mem 5981544
  have hl2 := Util.readLE8_lt s.mem 5981552
  have hl3 := Util.readLE8_lt s.mem 5981560
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981536 0 1025900813667802212 2089005733004138687 159309191 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981544 8 = 1025900813667802212 := hT1'
  have hT2 : s.mem.readLE 5981552 8 = 2089005733004138687 := hT2'
  have hT3 : s.mem.readLE 5981560 8 = 159309191 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981536 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 0 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981536 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981544 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 1025900813667802212 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981544 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981552 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2089005733004138687 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981552 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981560 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159309191 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981560 8) = T3 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET3
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE (x.toNat + 24) 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT0, hwT1, hwT2, hwT3, hw0, hw1, hw2, hw3]
  all_goals (
    simp only [valueAt, Util.readLE_32]
    (try simp only [Util.dec_ite] at hbr)
    (repeat' split at *) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr) <;> first | omega | exact (hbr trivial).elim)

end Fv256.Amd64.Log10
