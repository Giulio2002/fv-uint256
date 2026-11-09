import Extracted
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.FormatFastFacts

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

set_option hygiene false in
macro "fin_big2" : tactic => `(tactic| exact ReachesRet.done (by simp [Extracted.entry])
  (finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl))


/-- the verb switch at `Format+0x11c`: `d`, `s`, `v` to the `Dec` path -/
theorem sw_dec (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x11c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) (hch : ch32 = 100 ∨ ch32 = 115 ∨ ch32 = 118) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x139)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  rcases hch with h | h | h
  all_goals (janus64_run [i68, hwa, h, BitVec.msb_eq_decide] until [Extracted.entry + 0x139]
             exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl))

/-- the verb switch at `Format+0x11c`: `x` to the `Hex` path -/
theorem sw_hex (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x11c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) (hch : ch32 = 120) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x176)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S') := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  janus64_run [i68, hwa, hch, BitVec.msb_eq_decide] until [Extracted.entry + 0x176]
  exact ReachesRet.done (by simp [Extracted.entry]) (finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl)

/-- the verb switch at `Format+0x11c`: any other verb to the big path -/
theorem sw_big (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x11c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) (h1 : ch32 ≠ 100) (h2 : ch32 ≠ 115) (h3 : ch32 ≠ 118) (h4 : ch32 ≠ 120) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1cc)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧ S'.mem = S.mem) := by
  obtain ⟨-, -, -, -, -, -, -, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨-, -, -, -, hal, hwb, hwn, -⟩ := hpre
  have f1 : ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 ch32)) - 100#32 = 0#32) :=
    fun h => h1 ((sub32_eq_zero _ 100 hlt (by decide)).1 h)
  have f2 : ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 ch32)) - 115#32 = 0#32) :=
    fun h => h2 ((sub32_eq_zero _ 115 hlt (by decide)).1 h)
  have f3 : ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 ch32)) - 118#32 = 0#32) :=
    fun h => h3 ((sub32_eq_zero _ 118 hlt (by decide)).1 h)
  have f4 : ¬ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 ch32)) - 120#32 = 0#32) :=
    fun h => h4 ((sub32_eq_zero _ 120 hlt (by decide)).1 h)
  janus64_run [i68, hwa, f1, f2, f3, f4, BitVec.msb_eq_decide] until [Extracted.entry + 0x1cc]
  all_goals exact ReachesRet.done (by simp [Extracted.entry]) ⟨finv_of hi' (by simp [setRegF_apply]) (by simp [setRegF_apply]) (by simp [setRegF_apply]) rfl (by simp [idf]) rfl rfl, rfl⟩

end Fv256.Amd64.FormatFast
