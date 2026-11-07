import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

set_option hygiene false in
/-- close a branch segment that ends at the target with `FInv` unchanged (`hi'`, `idf` in scope) -/
macro "fin_big" : tactic => `(tactic| exact ReachesRet.done (by simp [Extracted.entry])
  ⟨finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl, rfl⟩)

set_option hygiene false in
macro "fin_cont" : tactic => `(tactic| exact ReachesRet.done (by simp [Extracted.entry])
  ⟨finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl,
    by simp [setRegF_apply], by simp [setRegF_apply], rfl⟩)


theorem p_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x78))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 3).toNat % 256 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x85)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (S.regs 3) = 0#8 := (setWidth8_eq_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x85]
  fin_cont


theorem p_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x78))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 3).toNat % 256 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (S.regs 3) = 0#8 := fun h => hb ((setWidth8_eq_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big


theorem f1_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x9a))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xa2)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (S.regs 0) = 0#8 := (setWidth8_eq_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0xa2]
  fin_cont


theorem f1_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x9a))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (S.regs 0) = 0#8 := fun h => hb ((setWidth8_eq_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big


theorem f2_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xb7))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xbf)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (S.regs 0) = 0#8 := (setWidth8_eq_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0xbf]
  fin_cont


theorem f2_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xb7))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (S.regs 0) = 0#8 := fun h => hb ((setWidth8_eq_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big


theorem f4_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xf4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 = 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xfc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (S.regs 0) = 0#8 := (setWidth8_eq_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0xfc]
  fin_cont


theorem f4_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xf4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 ≠ 0) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (S.regs 0) = 0#8 := fun h => hb ((setWidth8_eq_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big



theorem f3_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xd4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 ≠ 1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0xdf)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (S.regs 0) ^^^ 1#32)) = 0#8 := fun h => hb ((xor1_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0xdf]
  fin_cont


theorem f3_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0xd4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 = 1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (S.regs 0) ^^^ 1#32)) = 0#8 := (xor1_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big


theorem f5_cont (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x111))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 ≠ 1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x11c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.regs 3 = S.regs 3 ∧ S'.regs 7 = S.regs 7 ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : ¬ BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (S.regs 0) ^^^ 1#32)) = 0#8 := fun h => hb ((xor1_zero _).1 h)
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x11c]
  fin_cont


theorem f5_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x111))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hb : (S.regs 0).toNat % 256 = 1) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hb' : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (S.regs 0) ^^^ 1#32)) = 0#8 := (xor1_zero _).2 hb
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [hb', i68, hwa] until [Extracted.entry + 0x1cc]
  fin_big

end Fv256.Amd64.FormatFast
