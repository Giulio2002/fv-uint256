import Extracted
import Fv256.GrabRet
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- site `f1`: call through the itab, return at `Format+0x9a` -/
theorem f1_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x85))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x9a)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j3 j1, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 7) j0 j3 j1 ∧ S'.regs 0 = j0 ∧ S'.regs 3 = j3) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr, hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfF
  have hwb0 := hwb
  have hout0 := hout
  janus64_run [i58, i60, ht18, hta, hwa] until [Extracted.entry + 0x9a] calls [hC]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 3, junk 1, hR, ?_, ?_⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · exact finv_call hi' hwb0 hout0 (by omega) hfr (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
      (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
      (by simp [retState64]) (by simp [retState64, idf]) (by simp [retState64]) rfl
  · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [retState64, callRegs64_apply, setRegF_apply]) rfl
    have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    show Janus.Contracts.view R2.rt L (S.mem.writeLE _ 8 _) = _
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retState64, callRegs64_apply]
  · simp [retState64, callRegs64_apply]


/-- site `f2`: call through the itab, return at `Format+0xb7` -/
theorem f2_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xa2))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xb7)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j3 j1, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 7) j0 j3 j1 ∧ S'.regs 0 = j0 ∧ S'.regs 3 = j3) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr, hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfF
  have hwb0 := hwb
  have hout0 := hout
  janus64_run [i58, i60, ht18, hta, hwa] until [Extracted.entry + 0xb7] calls [hC]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 3, junk 1, hR, ?_, ?_⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · exact finv_call hi' hwb0 hout0 (by omega) hfr (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
      (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
      (by simp [retState64]) (by simp [retState64, idf]) (by simp [retState64]) rfl
  · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [retState64, callRegs64_apply, setRegF_apply]) rfl
    have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    show Janus.Contracts.view R2.rt L (S.mem.writeLE _ 8 _) = _
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retState64, callRegs64_apply]
  · simp [retState64, callRegs64_apply]


/-- site `f3`: call through the itab, return at `Format+0xd4` -/
theorem f3_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xbf))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xd4)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j3 j1, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 7) j0 j3 j1 ∧ S'.regs 0 = j0 ∧ S'.regs 3 = j3) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr, hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfF
  have hwb0 := hwb
  have hout0 := hout
  janus64_run [i58, i60, ht18, hta, hwa] until [Extracted.entry + 0xd4] calls [hC]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 3, junk 1, hR, ?_, ?_⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · exact finv_call hi' hwb0 hout0 (by omega) hfr (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
      (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
      (by simp [retState64]) (by simp [retState64, idf]) (by simp [retState64]) rfl
  · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [retState64, callRegs64_apply, setRegF_apply]) rfl
    have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    show Janus.Contracts.view R2.rt L (S.mem.writeLE _ 8 _) = _
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retState64, callRegs64_apply]
  · simp [retState64, callRegs64_apply]


/-- site `f4`: call through the itab, return at `Format+0xf4` -/
theorem f4_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xdf))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xf4)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j3 j1, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 7) j0 j3 j1 ∧ S'.regs 0 = j0 ∧ S'.regs 3 = j3) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr, hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfF
  have hwb0 := hwb
  have hout0 := hout
  janus64_run [i58, i60, ht18, hta, hwa] until [Extracted.entry + 0xf4] calls [hC]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 3, junk 1, hR, ?_, ?_⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · exact finv_call hi' hwb0 hout0 (by omega) hfr (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
      (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
      (by simp [retState64]) (by simp [retState64, idf]) (by simp [retState64]) rfl
  · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [retState64, callRegs64_apply, setRegF_apply]) rfl
    have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    show Janus.Contracts.view R2.rt L (S.mem.writeLE _ 8 _) = _
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retState64, callRegs64_apply]
  · simp [retState64, callRegs64_apply]


/-- site `f5`: call through the itab, return at `Format+0x111` -/
theorem f5_call (impl : List Amd64.Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract64 (Extracted.program.link impl) fF 2 stack 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xfc))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x111)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j3 j1, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 7) j0 j3 j1 ∧ S'.regs 0 = j0 ∧ S'.regs 3 = j3) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0, h3, h1, h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr, hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfF
  have hwb0 := hwb
  have hout0 := hout
  janus64_run [i58, i60, ht18, hta, hwa] until [Extracted.entry + 0x111] calls [hC]
  fv_ret_names junk f x yh m zh kr hpr hfr hR
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 3, junk 1, hR, ?_, ?_⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · exact finv_call hi' hwb0 hout0 (by omega) hfr (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
      (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
      (by simp [retState64]) (by simp [retState64, idf]) (by simp [retState64]) rfl
  · refine rpres_call hpr (by simp [setRegF_apply]) (fun L => ?_) (by simp [retState64, callRegs64_apply, setRegF_apply]) rfl
    have hO : ∀ a n, (S0.regs 4).toNat - 8 - stack ≤ a → a + n ≤ (S0.regs 4).toNat - 8 - stack + (stack + 128) → Outside a n R2.rt :=
      fun a n h1 h2 => hwR.of_sub h1 h2
    show Janus.Contracts.view R2.rt L (S.mem.writeLE _ 8 _) = _
    rw [Janus.Contracts.view_writeLE_out (hO _ _ (by omega) (by omega))]
  · simp [retState64, callRegs64_apply]
  · simp [retState64, callRegs64_apply]


end Fv256.Amd64.FormatFast
