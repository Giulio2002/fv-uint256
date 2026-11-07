import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatFastW
import Fv256.Arm64.FormatFastPF
import Fv256.Arm64.FormatFastB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

set_option linter.unusedVariables false

namespace Fv256.Arm64.FormatFast

theorem p_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RP : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x60))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x7c, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RP data (BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3) j0 j1 j2 ∧ j1.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RP data (BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3) j0 j1 j2 ∧ ¬ j1.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RP data (BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3) j0 j1 j2) (fun j0 j1 => j1.toNat % 2 = 0) H hH
    (rr_mono (p_call impl R2 rt stack fW fP fF fWr RP z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (p_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (p_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem f1_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x7c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x9c, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ j0.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ ¬ j0.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2) (fun j0 j1 => j0.toNat % 2 = 0) H hH
    (rr_mono (f1_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (f1_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (f1_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem f2_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x9c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xbc, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ j0.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ ¬ j0.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2) (fun j0 j1 => j0.toNat % 2 = 0) H hH
    (rr_mono (f2_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (f2_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (f2_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem f3_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xbc))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0xe0, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ j0.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ ¬ j0.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2) (fun j0 j1 => j0.toNat % 2 = 0) H hH
    (rr_mono (f3_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (f3_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (f3_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem f4_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xe0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x100, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ j0.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ ¬ j0.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2) (fun j0 j1 => j0.toNat % 2 = 0) H hH
    (rr_mono (f4_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (f4_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (f4_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem f5_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (H : Prop) (hH : H)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x100))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) (hk : RPres R2 S0 S) :
    RT (Extracted.program.link impl) S
      [(Extracted.entry + 0x11c, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ j0.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S') ∧ H ∧
          ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ ¬ j0.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2) (fun j0 j1 => j0.toNat % 2 = 0) H hH
    (rr_mono (f5_call impl R2 rt stack fW fP fF fWr RF z tab data ch32 hC S0 S hpc hpre hi)
      (fun S' h => ⟨⟨h.1, hk.trans h.2.1 hi.2.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (f5_cont impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (f5_big impl rt stack fW fP fF fWr z tab data ch32 S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

theorem w_site (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RW : Res)
    (z tab data : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True) (RtPreserves R2))
    (S0 : State) (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside (S0.sp.toNat - stack) (stack + 0x78) R2.rt) :
    RT (Extracted.program.link impl) S0
      [(Extracted.entry + 0x60, fun S' => (FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ RPres R2 S0 S') ∧ True ∧
          ∃ j0 j1 j2, RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2 ∧ j1.toNat % 2 = 0),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ RPres R2 S0 S') ∧ True ∧
          ∃ j0 j1 j2, RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2 ∧ ¬ j1.toNat % 2 = 0)] :=
  site_rt (Qi := fun S' => FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ RPres R2 S0 S')
    (fun j0 j1 j2 => RW data (BitVec.ofNat 64 fW) data (S0.regs 3) j0 j1 j2) (fun j0 j1 => j1.toNat % 2 = 0) True trivial
    (rr_mono (w_call impl R2 rt stack fW fP fF fWr RW z tab data hW S0 hpc hpre hwR) (fun S' h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩))
    (fun S' hr hq hb => rr_mono (w_cont impl rt stack fW fP fF fWr z tab data _ S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))
    (fun S' hr hq hb => rr_mono (w_big impl rt stack fW fP fF fWr z tab data _ S0 S' hr hpre hq.1 hb)
      (fun S'' h => ⟨h.1, hq.2.trans (RPres.of_mem h.2) hq.1.2.2.1⟩))

end Fv256.Arm64.FormatFast
