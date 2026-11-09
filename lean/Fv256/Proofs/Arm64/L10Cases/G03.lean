import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem c0_34 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 33 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 34)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 30 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 34 := Util.bitLen_of_range _ 34 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773104 8 = 10000000000 := by simpa using hT64.2 10 (by decide)
  have hTa : s.mem.accessible 1773104 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_35 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 34 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 35)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 29 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 35 := Util.bitLen_of_range _ 35 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773104 8 = 10000000000 := by simpa using hT64.2 10 (by decide)
  have hTa : s.mem.accessible 1773104 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_36 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 35 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 36)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 28 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 36 := Util.bitLen_of_range _ 36 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773112 8 = 100000000000 := by simpa using hT64.2 11 (by decide)
  have hTa : s.mem.accessible 1773112 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_37 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 36 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 37)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 27 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 37 := Util.bitLen_of_range _ 37 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773112 8 = 100000000000 := by simpa using hT64.2 11 (by decide)
  have hTa : s.mem.accessible 1773112 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_38 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 37 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 38)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 26 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 38 := Util.bitLen_of_range _ 38 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773112 8 = 100000000000 := by simpa using hT64.2 11 (by decide)
  have hTa : s.mem.accessible 1773112 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_39 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 38 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 39)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 25 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 39 := Util.bitLen_of_range _ 39 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773120 8 = 1000000000000 := by simpa using hT64.2 12 (by decide)
  have hTa : s.mem.accessible 1773120 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_40 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 39 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 40)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 24 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 40 := Util.bitLen_of_range _ 40 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773120 8 = 1000000000000 := by simpa using hT64.2 12 (by decide)
  have hTa : s.mem.accessible 1773120 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_41 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 40 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 41)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 23 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 41 := Util.bitLen_of_range _ 41 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773120 8 = 1000000000000 := by simpa using hT64.2 12 (by decide)
  have hTa : s.mem.accessible 1773120 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_42 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 41 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 42)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 22 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 42 := Util.bitLen_of_range _ 42 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773120 8 = 1000000000000 := by simpa using hT64.2 12 (by decide)
  have hTa : s.mem.accessible 1773120 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_43 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 42 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 43)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 21 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 43 := Util.bitLen_of_range _ 43 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773128 8 = 10000000000000 := by simpa using hT64.2 13 (by decide)
  have hTa : s.mem.accessible 1773128 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_44 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 43 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 44)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 20 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 44 := Util.bitLen_of_range _ 44 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773128 8 = 10000000000000 := by simpa using hT64.2 13 (by decide)
  have hTa : s.mem.accessible 1773128 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_45 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 44 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 45)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 19 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 45 := Util.bitLen_of_range _ 45 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773128 8 = 10000000000000 := by simpa using hT64.2 13 (by decide)
  have hTa : s.mem.accessible 1773128 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_46 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 45 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 46)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 18 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 46 := Util.bitLen_of_range _ 46 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773136 8 = 100000000000000 := by simpa using hT64.2 14 (by decide)
  have hTa : s.mem.accessible 1773136 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_47 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 46 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 47)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 17 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 47 := Util.bitLen_of_range _ 47 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773136 8 = 100000000000000 := by simpa using hT64.2 14 (by decide)
  have hTa : s.mem.accessible 1773136 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_48 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 47 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 48)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 16 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 48 := Util.bitLen_of_range _ 48 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773136 8 = 100000000000000 := by simpa using hT64.2 14 (by decide)
  have hTa : s.mem.accessible 1773136 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_49 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 48 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 49)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 15 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 49 := Util.bitLen_of_range _ 49 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773144 8 = 1000000000000000 := by simpa using hT64.2 15 (by decide)
  have hTa : s.mem.accessible 1773144 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_50 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 49 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 50)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 14 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 50 := Util.bitLen_of_range _ 50 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773144 8 = 1000000000000000 := by simpa using hT64.2 15 (by decide)
  have hTa : s.mem.accessible 1773144 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

end Fv256.Arm64.Log10
