import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.GrabRetA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.GrabRetA64

namespace Fv256.Arm64.FormatFast

/-- site `p`: call through the itab, return at `Format+0x70` -/
theorem p_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RP : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x60))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x70)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RP data (BitVec.ofNat 64 fP) (S.regs 2) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfP
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht20, hta, hwa, i4] until [Extracted.entry + 0x70] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

/-- site `f1`: call through the itab, return at `Format+0x90` -/
theorem f1_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x7c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x90)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2b) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfF
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht18, hta, hwa, i4] until [Extracted.entry + 0x90] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

/-- site `f2`: call through the itab, return at `Format+0xb0` -/
theorem f2_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x9c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xb0)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x20) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfF
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht18, hta, hwa, i4] until [Extracted.entry + 0xb0] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

/-- site `f3`: call through the itab, return at `Format+0xd0` -/
theorem f3_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xbc))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xd0)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x2d) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfF
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht18, hta, hwa, i4] until [Extracted.entry + 0xd0] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

/-- site `f4`: call through the itab, return at `Format+0xf4` -/
theorem f4_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xe0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xf4)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x30) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfF
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht18, hta, hwa, i4] until [Extracted.entry + 0xf4] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

/-- site `f5`: call through the itab, return at `Format+0x114` -/
theorem f5_call (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RF : Res)
    (z tab data : BitVec 64) (ch32 : Nat)
    (hC : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x100))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x114)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ RPres R2 S S' ∧
        ∃ j0 j1 j2, RF data (BitVec.ofNat 64 0x23) (BitVec.ofNat 64 fF) (S.regs 3) j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  simp only [CodePtrOK] at hfF
  have hout8 : Outside (S0.sp.toNat - 8) 128 rt := hout.of_sub (by omega) (by omega)
  janus_run [i96, i104, ht18, hta, hwa, i4] until [Extracted.entry + 0x114] calls [hC]
  fv_ret_names_a64 junk f v m ex ep hk1 hpr hfr hR
  refine ReachesRet.done ?_ ⟨?_, ?_, junk 0, junk 1, junk 2, hR, ?_, ?_⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call (m := m) hi' hst hout ?_ hfr ?_ ?_ ?_ ?_ rfl
    · omega
    all_goals simp [retStateX, callRegs_apply, setReg_apply, i4]
  · exact rpres_call hpr (by simp [setReg_apply]) (fun L => rfl) rfl
  · simp [retStateX, callRegs_apply, setReg_apply]
  · simp [retStateX, callRegs_apply, setReg_apply]

end Fv256.Arm64.FormatFast
