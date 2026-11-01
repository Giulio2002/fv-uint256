import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Amd64.L10Defs

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Log10

set_option maxHeartbeats 64000000 in
theorem c0_53 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 8 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧
        (5967168 + 160 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ 5967168) ∧
        (5971840 + 1920 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ 5971840) ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 52 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 53)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ valueAt s x 32 ∧ valueAt s x 32 < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hge, hnw, hacc⟩, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hge hacc hnw hdis hd64 hdB
  have hc : Janus.Arm64.clzNat 64 (s.mem.readLE x.toNat 8) = 11 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 53 := Util.bitLen_of_range _ 53 (by omega) (by omega) (by omega)
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
  have hTv : s.mem.readLE 5967296 8 = 10000000000000000 := by simpa using hT64.2 16 (by decide)
  have hTa : s.mem.accessible 5967296 8 false = true := Janus.Arm64.Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  obtain ⟨T, hET⟩ : ∃ T, s.mem.readLE 5967296 8 = T := ⟨_, rfl⟩
  have hVT : T = 10000000000000000 := by rw [← hET]; exact hTv
  have hBT : T < 18446744073709551616 := by rw [hVT]; decide
  have hwT : ∀ v, ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 v).readLE 5967296 8) = T := fun v => by
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact hET
  have b0 := Util.readLE8_lt s.mem x.toNat
  have b1 := Util.readLE8_lt s.mem (x.toNat + 8)
  have b2 := Util.readLE8_lt s.mem (x.toNat + 16)
  have b3 := Util.readLE8_lt s.mem (x.toNat + 24)
  have hne : s.mem.readLE x.toNat 8 ≠ 0 := by omega
  janus64_run [Util.cmp_eq_mod, hne, hwr, hc, hwT, hz3, hz2, hz1, hw0, hw1, hw2, hw3]
  all_goals (simp only [valueAt, Util.readLE_32]; omega)

end Fv256.Amd64.Log10
