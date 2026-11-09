import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Arm64.FormatFastBigA
import Fv256.Proofs.Arm64.FormatFastBigB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.IntoBig Fv256.Arm64.IntoBig

namespace Fv256.Arm64.FormatFast

/-- **(iii) the big path, arm64.**  From `S` at `Format+0x204` (the big-path label) with `FPre`/`FInv` (the state of (ii)'s second exit) and the allocator facts
IntoBig needs: `*slot = 0`, `IntoBig(z, &slot)`, then the static call `math/big.(*Int).Format(b, s, ch)` where `b` is a `big.Int` object of value
`val256 z` (the call-site property of `hBf`, proved here), epilogue, return. -/
theorem big_path (impl : List Segment) (hI : ImplApart Extracted.program impl) (R : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (rt rtF : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RBf : Res) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State)
    (hBf : ICallContract (Extracted.program.link impl) fmtAddr 4 stack 120 rtF (fun _ => []) RBf
      (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ BigObj sc.mem P (val256 S0.mem z.toNat) ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch32))
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x204))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) (h4608 : 4608 ≤ stack) (hz0 : z.toNat ≠ 0)
    (hdl : Extracted.program.DataLoaded S.mem) (hg : GuardOK S 4144)
    (hgd : (S.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S.regs 28).toNat + 16)
    (hgr : Outside ((S.regs 28).toNat + 16) 8 R.rt)
    (hfl : S.mem.accessible flagAddr 4 false = true) (ht1 : Outside bigType 16 R.rt) (ht2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b0 [] (S.regs 28).toNat (view R.rt [] S.mem)) (hbud : blockSize 32 false + blockSize 32 true ≤ b0)
    (hRout : Outside (S0.sp.toNat - stack) (stack + 0x78) R.rt) (hzR : Outside z.toNat 32 R.rt)
    (hoF : Outside (S0.sp.toNat - 8) 128 rtF) (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S
      (fun S' => S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
        S'.regs 28 = S.regs 28 ∧ S'.regs 18 = S.regs 18 ∧
        MemFrame S.mem S'.mem (R.rt ++ rtF ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 56)]) ∧
        (∃ P j0 j1 j2, RBf (BitVec.ofNat 64 P) tab data
          (BitVec.ofNat 64 (if ch32 < 2 ^ 31 then ch32 else ch32 + 18446744069414584320)) j0 j1 j2)) := by
  have hpre0 := hpre
  obtain ⟨-, -, -, -, hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre0
  obtain ⟨-, -, -, -, -, -, -, hwaS⟩ := finv_tab hpre hi
  obtain ⟨-, -, -, -, -, hzr, -⟩ := (finv_tab hpre hi)
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  have hspn : S.sp.toNat = S0.sp.toNat := by rw [i4]
  refine rr_trans (big_a impl hI R b0 hnew hwb1 hwb2 rt stack fW fP fF fWr z tab data ch32 S0 S hpc hpre ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩
    h4608 hz0 hdl hg (by unfold Apart; omega) hgr hfl ht1 ht2 hok1 hok2 hok3 hok4 hinv hbud hRout hzR (by unfold Apart; omega)) ?_
  intro S1 hr1 hq1
  obtain ⟨hs1, h29, h28, h18, ⟨P, hbo⟩, hfrA⟩ := hq1
  have hsp0 : S1.sp = S0.sp := hs1.trans i4
  have hoA : ∀ a n, (a + n ≤ S0.sp.toNat - 4144 ∨ S0.sp.toNat - 8 ≤ a) → (a + n ≤ S0.sp.toNat + 8 ∨ S0.sp.toNat + 24 ≤ a) →
      (a + n ≤ S0.sp.toNat + 48 ∨ S0.sp.toNat + 56 ≤ a) → S0.sp.toNat - stack ≤ a → a + n ≤ S0.sp.toNat + 0x78 →
      Outside a n (R.rt ++ [(S0.sp.toNat - 4144, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 24),
        (S0.sp.toNat + 48, S0.sp.toNat + 56)]) := by
    intro a n h1 h2 h3 h4 h5
    simp only [outside_append, outside_cons, outside_nil]
    exact ⟨hRout.of_sub h4 (by omega), h1, h2, h3, trivial⟩
  have hs48 : S1.mem.readLE (S0.sp.toNat + 48) 8 = P := hbo.choose_spec.choose_spec.choose_spec.1
  have hP : P < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt S1.mem (S0.sp.toNat + 48) 8
    rw [hs48] at this; simpa using this
  have hr0 : S1.mem.readLE S0.sp.toNat 8 = S0.mem.readLE S0.sp.toNat 8 := by
    rw [hfrA.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact ifr.readLE _ _ (out_fl_save (hout.of_sub (by omega) (by omega)) (by omega) (by omega) hst)
  have hr8 : S1.mem.readLE (S0.sp.toNat - 8) 8 = S0.mem.readLE (S0.sp.toNat - 8) 8 := by
    rw [hfrA.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega) (by omega))]
    exact ifr.readLE _ _ (out_fl_save (hout.of_sub (by omega) (by omega)) (by omega) (by omega) hst)
  have hsp' : ∀ a n, S0.sp.toNat + 88 ≤ a → a + n ≤ S0.sp.toNat + 116 → S1.mem.readLE a n = S.mem.readLE a n := fun a n h1 h2 =>
    hfrA.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
  have hwa1 : S1.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true := by rw [hfrA.accessible]; exact hwaS
  have hBO : BigObj S1.mem P (val256 S0.mem z.toNat) := BigObj.of_bigOut hbo
  refine rr_mono (big_b impl rtF stack RBf tab data ch32 P (val256 S0.mem z.toNat) S0 S1 hBf hlt hBO hr1 hsp0 hal hst hwb hwn hwa1
    hoF hs48 hP (by rw [hsp' (S0.sp.toNat + 96) 8 (by omega) (by omega)]; exact i96) (by rw [hsp' (S0.sp.toNat + 104) 8 (by omega) (by omega)]; exact i104)
    (by rw [hsp' (S0.sp.toNat + 112) 4 (by omega) (by omega)]; exact i112) hr0 hr8 hret) (fun S' h => ?_)
  obtain ⟨a1, a2, a3, a4, hfrB, j0, j1, j2, hR⟩ := h
  refine ⟨a1, a2, a3.trans h28, a4.trans h18, ?_, P, j0, j1, j2, hR⟩
  have hfrB' : MemFrame S1.mem S'.mem (R.rt ++ rtF ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 56)]) :=
    MemFrame.mono hfrB (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨⟨h0, h1⟩, h2, h3, -⟩ := h
      exact ⟨h1, h2, by omega, trivial⟩)
  have hfrA' : MemFrame S.mem S1.mem (R.rt ++ rtF ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 56)]) :=
    MemFrame.mono hfrA (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨⟨h0, h1⟩, h2, h3, -⟩ := h
      refine ⟨h0, ?_, ?_, ?_, trivial⟩ <;> omega)
  exact hfrA'.trans hfrB' fun a n h => ⟨h, h⟩

end Fv256.Arm64.FormatFast
