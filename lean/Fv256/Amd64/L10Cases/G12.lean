import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c2_59 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 58 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 59)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 5 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 59 := Util.bitLen_of_range _ 59 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981216 32 = 100000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 36 (by decide)
  have hTa : s.mem.accessible 5981216 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981216
  have hl1 := Util.readLE8_lt s.mem 5981224
  have hl2 := Util.readLE8_lt s.mem 5981232
  have hl3 := Util.readLE8_lt s.mem 5981240
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981216 2377900603251621888 18302566799529756941 293873587705571876 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981224 8 = 18302566799529756941 := hT1'
  have hT2 : s.mem.readLE 5981232 8 = 293873587705571876 := hT2'
  have hT3 : s.mem.readLE 5981240 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981216 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2377900603251621888 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981216 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981224 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 18302566799529756941 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981224 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981232 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587705571876 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981232 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981240 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981240 8) = T3 := fun v => by
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
theorem c2_60 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 59 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 60)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 4 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 60 := Util.bitLen_of_range _ 60 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981216 32 = 100000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 36 (by decide)
  have hTa : s.mem.accessible 5981216 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981216
  have hl1 := Util.readLE8_lt s.mem 5981224
  have hl2 := Util.readLE8_lt s.mem 5981232
  have hl3 := Util.readLE8_lt s.mem 5981240
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981216 2377900603251621888 18302566799529756941 293873587705571876 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981224 8 = 18302566799529756941 := hT1'
  have hT2 : s.mem.readLE 5981232 8 = 293873587705571876 := hT2'
  have hT3 : s.mem.readLE 5981240 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981216 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 2377900603251621888 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981216 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981224 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 18302566799529756941 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981224 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981232 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 293873587705571876 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981232 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981240 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981240 8) = T3 := fun v => by
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
theorem c2_61 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 60 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 61)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 3 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 61 := Util.bitLen_of_range _ 61 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981248 32 = 1000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 37 (by decide)
  have hTa : s.mem.accessible 5981248 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981248
  have hl1 := Util.readLE8_lt s.mem 5981256
  have hl2 := Util.readLE8_lt s.mem 5981264
  have hl3 := Util.readLE8_lt s.mem 5981272
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981248 5332261958806667264 17004971331911604867 2938735877055718769 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981256 8 = 17004971331911604867 := hT1'
  have hT2 : s.mem.readLE 5981264 8 = 2938735877055718769 := hT2'
  have hT3 : s.mem.readLE 5981272 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981248 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 5332261958806667264 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981248 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981256 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17004971331911604867 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981256 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981264 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877055718769 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981264 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981272 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981272 8) = T3 := fun v => by
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
theorem c2_62 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 61 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 62)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 2 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 62 := Util.bitLen_of_range _ 62 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981248 32 = 1000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 37 (by decide)
  have hTa : s.mem.accessible 5981248 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981248
  have hl1 := Util.readLE8_lt s.mem 5981256
  have hl2 := Util.readLE8_lt s.mem 5981264
  have hl3 := Util.readLE8_lt s.mem 5981272
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981248 5332261958806667264 17004971331911604867 2938735877055718769 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981256 8 = 17004971331911604867 := hT1'
  have hT2 : s.mem.readLE 5981264 8 = 2938735877055718769 := hT2'
  have hT3 : s.mem.readLE 5981272 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981248 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 5332261958806667264 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981248 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981256 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17004971331911604867 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981256 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981264 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877055718769 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981264 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981272 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981272 8) = T3 := fun v => by
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
theorem c2_63 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 62 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 63)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 1 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 63 := Util.bitLen_of_range _ 63 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981248 32 = 1000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 37 (by decide)
  have hTa : s.mem.accessible 5981248 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981248
  have hl1 := Util.readLE8_lt s.mem 5981256
  have hl2 := Util.readLE8_lt s.mem 5981264
  have hl3 := Util.readLE8_lt s.mem 5981272
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981248 5332261958806667264 17004971331911604867 2938735877055718769 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981256 8 = 17004971331911604867 := hT1'
  have hT2 : s.mem.readLE 5981264 8 = 2938735877055718769 := hT2'
  have hT3 : s.mem.readLE 5981272 8 = 0 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981248 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 5332261958806667264 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981248 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981256 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 17004971331911604867 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981256 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981264 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 2938735877055718769 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981264 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981272 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 0 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981272 8) = T3 := fun v => by
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
theorem c2_64 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 63 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 64)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 0 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 64 := Util.bitLen_of_range _ 64 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981280 32 = 10000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 38 (by decide)
  have hTa : s.mem.accessible 5981280 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981280
  have hl1 := Util.readLE8_lt s.mem 5981288
  have hl2 := Util.readLE8_lt s.mem 5981296
  have hl3 := Util.readLE8_lt s.mem 5981304
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981280 16429131440647569408 4029016655730084128 10940614696847636083 1 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981288 8 = 4029016655730084128 := hT1'
  have hT2 : s.mem.readLE 5981296 8 = 10940614696847636083 := hT2'
  have hT3 : s.mem.readLE 5981304 8 = 1 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981280 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16429131440647569408 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981280 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981288 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 4029016655730084128 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981288 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981296 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 10940614696847636083 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981296 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981304 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981304 8) = T3 := fun v => by
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
theorem c3_1 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 0 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 1)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 63 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 1 := Util.bitLen_of_range _ 1 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981280 32 = 10000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 38 (by decide)
  have hTa : s.mem.accessible 5981280 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981280
  have hl1 := Util.readLE8_lt s.mem 5981288
  have hl2 := Util.readLE8_lt s.mem 5981296
  have hl3 := Util.readLE8_lt s.mem 5981304
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981280 16429131440647569408 4029016655730084128 10940614696847636083 1 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981288 8 = 4029016655730084128 := hT1'
  have hT2 : s.mem.readLE 5981296 8 = 10940614696847636083 := hT2'
  have hT3 : s.mem.readLE 5981304 8 = 1 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981280 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16429131440647569408 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981280 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981288 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 4029016655730084128 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981288 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981296 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 10940614696847636083 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981296 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981304 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981304 8) = T3 := fun v => by
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
theorem c3_2 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 1 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 2)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 62 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 2 := Util.bitLen_of_range _ 2 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981280 32 = 10000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 38 (by decide)
  have hTa : s.mem.accessible 5981280 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981280
  have hl1 := Util.readLE8_lt s.mem 5981288
  have hl2 := Util.readLE8_lt s.mem 5981296
  have hl3 := Util.readLE8_lt s.mem 5981304
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981280 16429131440647569408 4029016655730084128 10940614696847636083 1 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981288 8 = 4029016655730084128 := hT1'
  have hT2 : s.mem.readLE 5981296 8 = 10940614696847636083 := hT2'
  have hT3 : s.mem.readLE 5981304 8 = 1 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981280 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16429131440647569408 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981280 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981288 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 4029016655730084128 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981288 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981296 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 10940614696847636083 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981296 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981304 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 1 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981304 8) = T3 := fun v => by
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
theorem c3_3 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 2 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 3)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 61 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 3 := Util.bitLen_of_range _ 3 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981312 32 = 100000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 39 (by decide)
  have hTa : s.mem.accessible 5981312 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981312
  have hl1 := Util.readLE8_lt s.mem 5981320
  have hl2 := Util.readLE8_lt s.mem 5981328
  have hl3 := Util.readLE8_lt s.mem 5981336
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981312 16717361816799281152 3396678409881738056 17172426599928602752 15 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981320 8 = 3396678409881738056 := hT1'
  have hT2 : s.mem.readLE 5981328 8 = 17172426599928602752 := hT2'
  have hT3 : s.mem.readLE 5981336 8 = 15 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981312 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16717361816799281152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981312 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981320 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 3396678409881738056 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981320 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981328 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 17172426599928602752 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981328 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981336 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981336 8) = T3 := fun v => by
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
theorem c3_4 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 3 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 4)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 60 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 4 := Util.bitLen_of_range _ 4 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981312 32 = 100000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 39 (by decide)
  have hTa : s.mem.accessible 5981312 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981312
  have hl1 := Util.readLE8_lt s.mem 5981320
  have hl2 := Util.readLE8_lt s.mem 5981328
  have hl3 := Util.readLE8_lt s.mem 5981336
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981312 16717361816799281152 3396678409881738056 17172426599928602752 15 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981320 8 = 3396678409881738056 := hT1'
  have hT2 : s.mem.readLE 5981328 8 = 17172426599928602752 := hT2'
  have hT3 : s.mem.readLE 5981336 8 = 15 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981312 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16717361816799281152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981312 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981320 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 3396678409881738056 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981320 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981328 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 17172426599928602752 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981328 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981336 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981336 8) = T3 := fun v => by
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
theorem c3_5 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 4 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 5)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 59 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 5 := Util.bitLen_of_range _ 5 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981312 32 = 100000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 39 (by decide)
  have hTa : s.mem.accessible 5981312 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981312
  have hl1 := Util.readLE8_lt s.mem 5981320
  have hl2 := Util.readLE8_lt s.mem 5981328
  have hl3 := Util.readLE8_lt s.mem 5981336
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981312 16717361816799281152 3396678409881738056 17172426599928602752 15 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981320 8 = 3396678409881738056 := hT1'
  have hT2 : s.mem.readLE 5981328 8 = 17172426599928602752 := hT2'
  have hT3 : s.mem.readLE 5981336 8 = 15 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981312 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16717361816799281152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981312 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981320 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 3396678409881738056 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981320 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981328 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 17172426599928602752 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981328 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981336 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981336 8) = T3 := fun v => by
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
theorem c3_6 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 5 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 6)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 58 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 6 := Util.bitLen_of_range _ 6 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981312 32 = 100000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 39 (by decide)
  have hTa : s.mem.accessible 5981312 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981312
  have hl1 := Util.readLE8_lt s.mem 5981320
  have hl2 := Util.readLE8_lt s.mem 5981328
  have hl3 := Util.readLE8_lt s.mem 5981336
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981312 16717361816799281152 3396678409881738056 17172426599928602752 15 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981320 8 = 3396678409881738056 := hT1'
  have hT2 : s.mem.readLE 5981328 8 = 17172426599928602752 := hT2'
  have hT3 : s.mem.readLE 5981336 8 = 15 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981312 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 16717361816799281152 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981312 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981320 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 3396678409881738056 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981320 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981328 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 17172426599928602752 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981328 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981336 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 15 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981336 8) = T3 := fun v => by
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
theorem c3_7 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 6 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 7)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 57 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 7 := Util.bitLen_of_range _ 7 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981344 32 = 1000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 40 (by decide)
  have hTa : s.mem.accessible 5981344 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981344
  have hl1 := Util.readLE8_lt s.mem 5981352
  have hl2 := Util.readLE8_lt s.mem 5981360
  have hl3 := Util.readLE8_lt s.mem 5981368
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981344 1152921504606846976 15520040025107828953 5703569335900062977 159 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981352 8 = 15520040025107828953 := hT1'
  have hT2 : s.mem.readLE 5981360 8 = 5703569335900062977 := hT2'
  have hT3 : s.mem.readLE 5981368 8 = 159 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981344 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1152921504606846976 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981344 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981352 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 15520040025107828953 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981352 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981360 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 5703569335900062977 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981360 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981368 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981368 8) = T3 := fun v => by
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
theorem c3_8 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 7 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 8)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 56 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 8 := Util.bitLen_of_range _ 8 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981344 32 = 1000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 40 (by decide)
  have hTa : s.mem.accessible 5981344 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981344
  have hl1 := Util.readLE8_lt s.mem 5981352
  have hl2 := Util.readLE8_lt s.mem 5981360
  have hl3 := Util.readLE8_lt s.mem 5981368
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981344 1152921504606846976 15520040025107828953 5703569335900062977 159 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981352 8 = 15520040025107828953 := hT1'
  have hT2 : s.mem.readLE 5981360 8 = 5703569335900062977 := hT2'
  have hT3 : s.mem.readLE 5981368 8 = 159 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981344 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1152921504606846976 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981344 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981352 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 15520040025107828953 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981352 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981360 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 5703569335900062977 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981360 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981368 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981368 8) = T3 := fun v => by
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
theorem c3_9 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 8 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 9)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 55 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 9 := Util.bitLen_of_range _ 9 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5981344 32 = 1000000000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 40 (by decide)
  have hTa : s.mem.accessible 5981344 32 false = true := Janus.Arm64.Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  have hl0 := Util.readLE8_lt s.mem 5981344
  have hl1 := Util.readLE8_lt s.mem 5981352
  have hl2 := Util.readLE8_lt s.mem 5981360
  have hl3 := Util.readLE8_lt s.mem 5981368
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 5981344 1152921504606846976 15520040025107828953 5703569335900062977 159 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 5981352 8 = 15520040025107828953 := hT1'
  have hT2 : s.mem.readLE 5981360 8 = 5703569335900062977 := hT2'
  have hT3 : s.mem.readLE 5981368 8 = 159 := hT3'
  obtain ⟨T0, hET0⟩ : ∃ T, s.mem.readLE 5981344 8 = T := ⟨_, rfl⟩
  have hVT0 : T0 = 1152921504606846976 := by rw [← hET0]; exact hT0
  have hBT0 : T0 < 18446744073709551616 := by rw [hVT0]; decide
  have hwT0 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981344 8) = T0 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET0
  obtain ⟨T1, hET1⟩ : ∃ T, s.mem.readLE 5981352 8 = T := ⟨_, rfl⟩
  have hVT1 : T1 = 15520040025107828953 := by rw [← hET1]; exact hT1
  have hBT1 : T1 < 18446744073709551616 := by rw [hVT1]; decide
  have hwT1 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981352 8) = T1 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET1
  obtain ⟨T2, hET2⟩ : ∃ T, s.mem.readLE 5981360 8 = T := ⟨_, rfl⟩
  have hVT2 : T2 = 5703569335900062977 := by rw [← hET2]; exact hT2
  have hBT2 : T2 < 18446744073709551616 := by rw [hVT2]; decide
  have hwT2 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981360 8) = T2 := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET2
  obtain ⟨T3, hET3⟩ : ∃ T, s.mem.readLE 5981368 8 = T := ⟨_, rfl⟩
  have hVT3 : T3 = 159 := by rw [← hET3]; exact hT3
  have hBT3 : T3 < 18446744073709551616 := by rw [hVT3]; decide
  have hwT3 : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5981368 8) = T3 := fun v => by
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
theorem c3_10 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 9 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 10)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 54 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 10 := Util.bitLen_of_range _ 10 (by omega) (by omega) (by omega)
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
theorem c3_11 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
        (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB) ∧
        2 ^ 10 ≤ s.mem.readLE (x.toNat + 24) 8 ∧ s.mem.readLE (x.toNat + 24) 8 < 2 ^ 11)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hl1, hl2⟩
  janus64_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = 53 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) = 11 := Util.bitLen_of_range _ 11 (by omega) (by omega) (by omega)
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

end Fv256.Amd64.Log10
