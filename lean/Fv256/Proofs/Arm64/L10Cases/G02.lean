import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem c0_17 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 16 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 17)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 47 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 17 := Util.bitLen_of_range _ 17 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773064 8 = 100000 := by simpa using hT64.2 5 (by decide)
  have hTa : s.mem.accessible 1773064 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_18 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 17 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 18)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 46 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 18 := Util.bitLen_of_range _ 18 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773064 8 = 100000 := by simpa using hT64.2 5 (by decide)
  have hTa : s.mem.accessible 1773064 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_19 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 18 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 19)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 45 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 19 := Util.bitLen_of_range _ 19 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773072 8 = 1000000 := by simpa using hT64.2 6 (by decide)
  have hTa : s.mem.accessible 1773072 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_20 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 19 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 20)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 44 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 20 := Util.bitLen_of_range _ 20 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773072 8 = 1000000 := by simpa using hT64.2 6 (by decide)
  have hTa : s.mem.accessible 1773072 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_21 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 20 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 21)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 43 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 21 := Util.bitLen_of_range _ 21 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773072 8 = 1000000 := by simpa using hT64.2 6 (by decide)
  have hTa : s.mem.accessible 1773072 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_22 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 21 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 22)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 42 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 22 := Util.bitLen_of_range _ 22 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773072 8 = 1000000 := by simpa using hT64.2 6 (by decide)
  have hTa : s.mem.accessible 1773072 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_23 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 22 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 23)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 41 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 23 := Util.bitLen_of_range _ 23 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773080 8 = 10000000 := by simpa using hT64.2 7 (by decide)
  have hTa : s.mem.accessible 1773080 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_24 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 23 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 24)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 40 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 24 := Util.bitLen_of_range _ 24 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773080 8 = 10000000 := by simpa using hT64.2 7 (by decide)
  have hTa : s.mem.accessible 1773080 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_25 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 24 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 25)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 39 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 25 := Util.bitLen_of_range _ 25 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773080 8 = 10000000 := by simpa using hT64.2 7 (by decide)
  have hTa : s.mem.accessible 1773080 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_26 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 25 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 26)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 38 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 26 := Util.bitLen_of_range _ 26 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773088 8 = 100000000 := by simpa using hT64.2 8 (by decide)
  have hTa : s.mem.accessible 1773088 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_27 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 26 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 27)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 37 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 27 := Util.bitLen_of_range _ 27 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773088 8 = 100000000 := by simpa using hT64.2 8 (by decide)
  have hTa : s.mem.accessible 1773088 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_28 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 27 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 28)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 36 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 28 := Util.bitLen_of_range _ 28 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773088 8 = 100000000 := by simpa using hT64.2 8 (by decide)
  have hTa : s.mem.accessible 1773088 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_29 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 28 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 29)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 35 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 29 := Util.bitLen_of_range _ 29 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773096 8 = 1000000000 := by simpa using hT64.2 9 (by decide)
  have hTa : s.mem.accessible 1773096 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_30 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 29 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 30)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 34 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 30 := Util.bitLen_of_range _ 30 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773096 8 = 1000000000 := by simpa using hT64.2 9 (by decide)
  have hTa : s.mem.accessible 1773096 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_31 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 30 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 31)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 33 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 31 := Util.bitLen_of_range _ 31 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773096 8 = 1000000000 := by simpa using hT64.2 9 (by decide)
  have hTa : s.mem.accessible 1773096 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_32 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 31 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 32)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 32 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 32 := Util.bitLen_of_range _ 32 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773096 8 = 1000000000 := by simpa using hT64.2 9 (by decide)
  have hTa : s.mem.accessible 1773096 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

set_option maxHeartbeats 64000000 in
theorem c0_33 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 32 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 33)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 31 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 33 := Util.bitLen_of_range _ 33 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773104 8 = 10000000000 := by simpa using hT64.2 10 (by decide)
  have hTa : s.mem.accessible 1773104 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

end Fv256.Arm64.Log10
