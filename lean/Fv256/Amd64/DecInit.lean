import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- Entry of `(*Int).Dec` (the extraction's entry point). -/
abbrev decE : Nat := Extracted.entry
/-- The loop head of `Dec` (`MOVQ CX, 0x100(SP)`), `0x16c` bytes into the function. -/
abbrev decH : Nat := Extracted.entry + 0x16c

theorem zeros_tab : ∀ i, i < 98 → Extracted.data[3]!.bytes[i]! = 48 := by
  decide +kernel

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem dec_init (s : State) (hpc : s.rip = BitVec.ofNat 64 decE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : StackGuardOK s 0xf8) (hw : StackWritable s 0x178 0x8) (hal : (s.regs 4).toNat % 8 = 0)
    (hd : Extracted.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ (s.regs 4).toNat - 0x178 ∨ (s.regs 4).toNat + 8 ≤ zp)
    (hbig : s.mem.readLE (zp + 8) 8 ≠ 0 ∨ s.mem.readLE (zp + 16) 8 ≠ 0 ∨ s.mem.readLE (zp + 24) 8 ≠ 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decH) s (fun S' => True) := by
  have hc : decE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hwb, hwn, hwa⟩ := hw
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hzn, hza⟩ := hz
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal
  janus64_data hd [hwa]
  have l0 := Janus.Arm64.Memory.readLE_lt s.mem zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  have hnz : ((BitVec.ofNat 64 (s.mem.readLE zp 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE zp 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  have hnz2 : ((BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  janus64_run [e0, hnz, hnz2] until [decH]
  all_goals (try trace_state)
  all_goals sorry
end Fv256.Amd64.Dec
