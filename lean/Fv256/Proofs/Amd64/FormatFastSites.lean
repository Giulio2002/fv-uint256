import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts
import Fv256.Proofs.Amd64.FormatFastP
import Fv256.Proofs.Amd64.FormatFastF
import Fv256.Proofs.Amd64.FormatFastB

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

theorem p_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RP : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fP 1 stack 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x68))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) (b3 : BitVec 64) (hb3 : S.regs 3 = b3) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x85, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ j3.toNat % 256 = 0),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ j3.toNat % 256 ≠ 0)] := by
  refine RT.trans (RT.of_reachesRet (p_call impl R2 rt stack fW fP fF fWr RP z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j3.toNat % 256 = 0
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x85)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ j3.toNat % 256 = 0) :=
      ReachesRet.mono (p_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h3]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hb3 ▸ hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · skip
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ j3.toNat % 256 ≠ 0) :=
      ReachesRet.mono (p_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h3]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hb3 ▸ hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


theorem f1_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x85))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xa2, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0)] := by
  refine RT.trans (RT.of_reachesRet (f1_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j0.toNat % 256 = 0
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xa2)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0) :=
      ReachesRet.mono (f1_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · skip
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0) :=
      ReachesRet.mono (f1_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


theorem f2_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xa2))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xbf, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0)] := by
  refine RT.trans (RT.of_reachesRet (f2_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j0.toNat % 256 = 0
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xbf)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0) :=
      ReachesRet.mono (f2_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · skip
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0) :=
      ReachesRet.mono (f2_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


theorem f3_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xbf))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xdf, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 1),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 1)] := by
  refine RT.trans (RT.of_reachesRet (f3_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j0.toNat % 256 ≠ 1
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xdf)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 1) :=
      ReachesRet.mono (f3_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · have hb := Decidable.of_not_not hb
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 1) :=
      ReachesRet.mono (f3_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


theorem f4_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xdf))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xfc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0)] := by
  refine RT.trans (RT.of_reachesRet (f4_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j0.toNat % 256 = 0
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xfc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 0) :=
      ReachesRet.mono (f4_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · skip
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 0) :=
      ReachesRet.mono (f4_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


theorem f5_site (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xfc))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x11c, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 1),
       (Extracted.entry + 0x1cc, fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S' ∧ H ∧
          ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 1)] := by
  refine RT.trans (RT.of_reachesRet (f5_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi hwR)) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, hq2, j0, j3, j1, hR, h0, h3⟩ := hq
  by_cases hb : j0.toNat % 256 ≠ 1
  · have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x11c)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 ≠ 1) :=
      ReachesRet.mono (f5_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2.2.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · have hb := Decidable.of_not_not hb
    have k1 : ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S'
        (fun S'' => FInv rt stack z tab data ch32 S0 S'' ∧ RPres R2 S0 S'' ∧ H ∧ ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ j0.toNat % 256 = 1) :=
      ReachesRet.mono (f5_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hi2
        (by rw [h0]; exact hb)) (fun S'' h => ⟨h.1, rpres_step hk hq2 h.2 hi hi2, hH, S.regs 7, j0, j3, j1, hR, hb⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩

end Fv256.Amd64.FormatFast
