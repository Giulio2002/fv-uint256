import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem zero (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE x.toNat 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0)
      (fun s s' => (s'.regs 0).toNat = 0) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz0, hz1, hz2, hz3⟩
  janus_intro hs
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  janus_run [hz0, hz1, hz2, hz3]
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_1 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 0 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 1)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 63 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 1 := Util.bitLen_of_range _ 1 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773024 8 = 1 := by simpa using hT64.2 0 (by decide)
  have hTa : s.mem.accessible 1773024 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_2 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 1 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 2)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 62 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 2 := Util.bitLen_of_range _ 2 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773024 8 = 1 := by simpa using hT64.2 0 (by decide)
  have hTa : s.mem.accessible 1773024 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_3 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 2 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 3)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 61 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 3 := Util.bitLen_of_range _ 3 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773032 8 = 10 := by simpa using hT64.2 1 (by decide)
  have hTa : s.mem.accessible 1773032 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_4 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 3 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 4)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 60 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 4 := Util.bitLen_of_range _ 4 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773032 8 = 10 := by simpa using hT64.2 1 (by decide)
  have hTa : s.mem.accessible 1773032 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_5 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 4 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 5)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 59 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 5 := Util.bitLen_of_range _ 5 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773032 8 = 10 := by simpa using hT64.2 1 (by decide)
  have hTa : s.mem.accessible 1773032 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_6 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 5 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 6)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 58 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 6 := Util.bitLen_of_range _ 6 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773040 8 = 100 := by simpa using hT64.2 2 (by decide)
  have hTa : s.mem.accessible 1773040 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_7 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 6 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 7)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 57 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 7 := Util.bitLen_of_range _ 7 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773040 8 = 100 := by simpa using hT64.2 2 (by decide)
  have hTa : s.mem.accessible 1773040 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_8 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 7 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 8)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 56 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 8 := Util.bitLen_of_range _ 8 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773040 8 = 100 := by simpa using hT64.2 2 (by decide)
  have hTa : s.mem.accessible 1773040 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_9 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 8 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 9)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 55 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 9 := Util.bitLen_of_range _ 9 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773048 8 = 1000 := by simpa using hT64.2 3 (by decide)
  have hTa : s.mem.accessible 1773048 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_10 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 9 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 10)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 54 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 10 := Util.bitLen_of_range _ 10 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773048 8 = 1000 := by simpa using hT64.2 3 (by decide)
  have hTa : s.mem.accessible 1773048 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_11 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 10 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 11)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 53 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 11 := Util.bitLen_of_range _ 11 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773048 8 = 1000 := by simpa using hT64.2 3 (by decide)
  have hTa : s.mem.accessible 1773048 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_12 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 11 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 12)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 52 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 12 := Util.bitLen_of_range _ 12 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773048 8 = 1000 := by simpa using hT64.2 3 (by decide)
  have hTa : s.mem.accessible 1773048 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_13 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 12 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 13)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 51 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 13 := Util.bitLen_of_range _ 13 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773056 8 = 10000 := by simpa using hT64.2 4 (by decide)
  have hTa : s.mem.accessible 1773056 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_14 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 13 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 14)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 50 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 14 := Util.bitLen_of_range _ 14 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773056 8 = 10000 := by simpa using hT64.2 4 (by decide)
  have hTa : s.mem.accessible 1773056 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_15 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 14 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 15)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 49 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 15 := Util.bitLen_of_range _ 15 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773056 8 = 10000 := by simpa using hT64.2 4 (by decide)
  have hTa : s.mem.accessible 1773056 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_16 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 15 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 16)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 48 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 16 := Util.bitLen_of_range _ 16 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773064 8 = 100000 := by simpa using hT64.2 5 (by decide)
  have hTa : s.mem.accessible 1773064 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

end Fv256.Arm64.Log10
