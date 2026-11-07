import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64

namespace Fv256.Arm64.FormatFast

theorem w_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x5c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 1).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x60)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 1) 0 == true) = true) := fun h => by have := (lsb0_iff _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x60]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem w_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x5c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 1).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 1) 0 == true) = true := (lsb0_iff _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem p_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x70))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 1).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x7c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 1) 0 == false) = true := (lsb0_false _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x7c]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem p_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x70))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 1).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 1) 0 == false) = true) := fun h => by have := (lsb0_false _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f1_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x90))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x9c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 0) 0 == false) = true := (lsb0_false _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x9c]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f1_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x90))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 0) 0 == false) = true) := fun h => by have := (lsb0_false _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f2_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xb0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xbc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 0) 0 == false) = true := (lsb0_false _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0xbc]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f2_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xb0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 0) 0 == false) = true) := fun h => by have := (lsb0_false _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f3_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xd0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xe0)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 0 ^^^ 1#64) 0 == true) = true := (lsb0_xor _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0xe0]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f3_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xd0))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 0 ^^^ 1#64) 0 == true) = true) := fun h => by have := (lsb0_xor _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f4_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xf4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x100)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 0) 0 == false) = true := (lsb0_false _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x100]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f4_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0xf4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 0) 0 == false) = true) := fun h => by have := (lsb0_false _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f5_cont (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x114))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x11c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ ((BitVec.getLsbD (S.regs 0 ^^^ 1#64) 0 == false) = true) := fun h => by have := (lsb0_xor_false _).1 h; omega
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x11c]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

theorem f5_big (impl : List Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x114))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 2 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x204)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : (BitVec.getLsbD (S.regs 0 ^^^ 1#64) 0 == false) = true := (lsb0_xor_false _).2 (by omega)
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, -, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0, h1, h2, h29, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  janus_run [hb', i112, hwa, i4] until [Extracted.entry + 0x204]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [i4]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) rfl)

end Fv256.Arm64.FormatFast
