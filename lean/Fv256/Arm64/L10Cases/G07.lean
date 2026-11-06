import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem c1_38 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 37 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 38)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 26 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 38 := Util.bitLen_of_range _ 38 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777856 32 = 10000000000000000000000000000000 := by simpa using hTB.2 11 (by decide)
  have hTa : s.mem.accessible 1777856 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777856 13875954555633532928 542101086242 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777864 8 = 542101086242 := hT1'
  have hT2 : s.mem.readLE 1777872 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777880 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_39 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 38 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 39)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 25 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 39 := Util.bitLen_of_range _ 39 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777856 32 = 10000000000000000000000000000000 := by simpa using hTB.2 11 (by decide)
  have hTa : s.mem.accessible 1777856 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777856 13875954555633532928 542101086242 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777864 8 = 542101086242 := hT1'
  have hT2 : s.mem.readLE 1777872 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777880 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_40 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 39 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 40)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 24 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 40 := Util.bitLen_of_range _ 40 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777856 32 = 10000000000000000000000000000000 := by simpa using hTB.2 11 (by decide)
  have hTa : s.mem.accessible 1777856 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777856 13875954555633532928 542101086242 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777864 8 = 542101086242 := hT1'
  have hT2 : s.mem.readLE 1777872 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777880 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_41 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 40 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 41)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 23 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 41 := Util.bitLen_of_range _ 41 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777856 32 = 10000000000000000000000000000000 := by simpa using hTB.2 11 (by decide)
  have hTa : s.mem.accessible 1777856 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777856 13875954555633532928 542101086242 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777864 8 = 542101086242 := hT1'
  have hT2 : s.mem.readLE 1777872 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777880 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_42 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 41 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 42)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 22 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 42 := Util.bitLen_of_range _ 42 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777888 32 = 100000000000000000000000000000000 := by simpa using hTB.2 12 (by decide)
  have hTa : s.mem.accessible 1777888 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777888 9632337040368467968 5421010862427 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777896 8 = 5421010862427 := hT1'
  have hT2 : s.mem.readLE 1777904 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777912 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_43 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 42 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 43)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 21 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 43 := Util.bitLen_of_range _ 43 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777888 32 = 100000000000000000000000000000000 := by simpa using hTB.2 12 (by decide)
  have hTa : s.mem.accessible 1777888 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777888 9632337040368467968 5421010862427 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777896 8 = 5421010862427 := hT1'
  have hT2 : s.mem.readLE 1777904 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777912 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_44 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 43 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 44)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 20 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 44 := Util.bitLen_of_range _ 44 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777888 32 = 100000000000000000000000000000000 := by simpa using hTB.2 12 (by decide)
  have hTa : s.mem.accessible 1777888 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777888 9632337040368467968 5421010862427 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777896 8 = 5421010862427 := hT1'
  have hT2 : s.mem.readLE 1777904 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777912 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_45 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 44 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 45)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 19 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 45 := Util.bitLen_of_range _ 45 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777920 32 = 1000000000000000000000000000000000 := by simpa using hTB.2 13 (by decide)
  have hTa : s.mem.accessible 1777920 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777920 4089650035136921600 54210108624275 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777928 8 = 54210108624275 := hT1'
  have hT2 : s.mem.readLE 1777936 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777944 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_46 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 45 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 46)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 18 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 46 := Util.bitLen_of_range _ 46 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777920 32 = 1000000000000000000000000000000000 := by simpa using hTB.2 13 (by decide)
  have hTa : s.mem.accessible 1777920 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777920 4089650035136921600 54210108624275 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777928 8 = 54210108624275 := hT1'
  have hT2 : s.mem.readLE 1777936 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777944 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_47 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 46 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 47)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 17 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 47 := Util.bitLen_of_range _ 47 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777920 32 = 1000000000000000000000000000000000 := by simpa using hTB.2 13 (by decide)
  have hTa : s.mem.accessible 1777920 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777920 4089650035136921600 54210108624275 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777928 8 = 54210108624275 := hT1'
  have hT2 : s.mem.readLE 1777936 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777944 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_48 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 47 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 48)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 16 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 48 := Util.bitLen_of_range _ 48 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777952 32 = 10000000000000000000000000000000000 := by simpa using hTB.2 14 (by decide)
  have hTa : s.mem.accessible 1777952 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777952 4003012203950112768 542101086242752 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777960 8 = 542101086242752 := hT1'
  have hT2 : s.mem.readLE 1777968 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777976 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_49 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 48 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 49)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 15 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 49 := Util.bitLen_of_range _ 49 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777952 32 = 10000000000000000000000000000000000 := by simpa using hTB.2 14 (by decide)
  have hTa : s.mem.accessible 1777952 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777952 4003012203950112768 542101086242752 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777960 8 = 542101086242752 := hT1'
  have hT2 : s.mem.readLE 1777968 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777976 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_50 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 49 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 50)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 14 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 50 := Util.bitLen_of_range _ 50 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777952 32 = 10000000000000000000000000000000000 := by simpa using hTB.2 14 (by decide)
  have hTa : s.mem.accessible 1777952 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777952 4003012203950112768 542101086242752 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777960 8 = 542101086242752 := hT1'
  have hT2 : s.mem.readLE 1777968 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777976 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_51 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 50 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 51)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 13 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 51 := Util.bitLen_of_range _ 51 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777952 32 = 10000000000000000000000000000000000 := by simpa using hTB.2 14 (by decide)
  have hTa : s.mem.accessible 1777952 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777952 4003012203950112768 542101086242752 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777960 8 = 542101086242752 := hT1'
  have hT2 : s.mem.readLE 1777968 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1777976 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_52 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 51 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 52)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 12 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 52 := Util.bitLen_of_range _ 52 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777984 32 = 100000000000000000000000000000000000 := by simpa using hTB.2 15 (by decide)
  have hTa : s.mem.accessible 1777984 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777984 3136633892082024448 5421010862427522 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777992 8 = 5421010862427522 := hT1'
  have hT2 : s.mem.readLE 1778000 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1778008 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_53 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 52 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 53)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 11 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 53 := Util.bitLen_of_range _ 53 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777984 32 = 100000000000000000000000000000000000 := by simpa using hTB.2 15 (by decide)
  have hTa : s.mem.accessible 1777984 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777984 3136633892082024448 5421010862427522 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777992 8 = 5421010862427522 := hT1'
  have hT2 : s.mem.readLE 1778000 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1778008 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

set_option maxHeartbeats 64000000 in
theorem c1_54 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ 2 ^ 53 ≤ s.mem.readLE (x.toNat + 8) 8 ∧ s.mem.readLE (x.toNat + 8) 8 < 2 ^ 54)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 8) 8) = 10 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) = 54 := Util.bitLen_of_range _ 54 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1777984 32 = 100000000000000000000000000000000000 := by simpa using hTB.2 15 (by decide)
  have hTa : s.mem.accessible 1777984 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1777984 3136633892082024448 5421010862427522 0 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1777992 8 = 5421010862427522 := hT1'
  have hT2 : s.mem.readLE 1778000 8 = 0 := hT2'
  have hT3 : s.mem.readLE 1778008 8 = 0 := hT3'
  janus_run [hc, hz3, hz2]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

end Fv256.Arm64.Log10
