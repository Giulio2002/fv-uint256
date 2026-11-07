import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
import Fv256.UtilE
import Fv256.Amd64.FormatBigDefs
import Fv256.Amd64.FormatBigA
import Fv256.Amd64.FormatBigB

/-!
# `(*uint256.Int).Format`, big path (iii) (amd64): `big_path`

From the state `S` at `Format+0x1cc` (the second exit of the fast path (ii): `FPre`/`FInv`), `slot := 0`, `IntoBig(z, &slot)` (the verified library,
re-targeted at this extraction), then the static call `math/big.(*Int).Format(slot, tab, data, ch)` whose call-site property `P` says that the
argument is a `big.Int` object holding `*z`; epilogue, return. The shape is that of `hbig` in `Format.lean`; the runtime facts the `IntoBig`
call needs are `BigR2`, plus the stack-guard margin and the facts about the data/goroutine words listed in the hypotheses.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFast Fv256.IntoBig

namespace Fv256.Amd64.FormatBig

theorem ofNat_toNat64' (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]

set_option maxRecDepth 20000 in
theorem big_path (impl : List Amd64.Segment) (hI : ImplApart Extracted.program impl) (R2 : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract64 (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat)) (stack fW fP fF fWr zv : Nat) (RBf : Res) (z tab data ch : BitVec 64)
    (hBf : ICallContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 80 rt (fun _ => [])
      RBf (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ BigObj sc.mem P.toNat zv ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32))
    (S0 S : State) (hz : z.toNat ≠ 0)
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hzv : S0.mem.readLE z.toNat 32 = zv)
    (hrip : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x1cc))
    (hfi : FInv rt stack z tab data (ch.toNat % 2 ^ 32) S0 S)
    (h4568 : 4568 ≤ stack)
    (hwR : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) R2.rt)
    (hdl : Extracted.program.DataLoaded S.mem)
    (hg1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (hg2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (hgo : Outside ((S0.regs 14).toNat + 16) 8 rt)
    (hgd : (S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16)
    (hx0 : S0.xmm 15 = 0) (hdf0 : S0.df = false)
    (hbr : BigR2 R2 b0 z S0)
    (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47)
    (hinv : R2.inv b0 [] (S.regs 14).toNat (view R2.rt [] S.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
      (BigQ R2 rt stack RBf tab data ch S0) := by
  have hft := finv_tab hpre hfi
  obtain ⟨-, -, -, -, -, -, -, hwaS⟩ := hft
  have hpre1 := hpre
  obtain ⟨-, -, -, -, hal, hwb, hwn, -, hout, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hpre1
  have hfi' := hfi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hfi'
  refine Fv256.E.reachesRet_bind' (big_A impl hI R2 b0 hnew hwb1 hwb2 rt stack fW fP fF fWr z tab data _ S0 S hz hpre hrip hfi h4568 hwR hdl hg1 hg2 hgo hgd
    hx0 hdf0 hbr hinv) ?_
  intro S1 hpc1 hS1
  obtain ⟨m4, m5, m14, mx, mfr, P, hs28, hBO, hPin, hAin⟩ := hS1
  have hr : (S0.regs 4).toNat = (S.regs 4).toNat := by rw [i4]
  rw [← hr] at mfr hs28
  have hP : P < 2 ^ 64 := by
    have := Janus.Arm64.Memory.readLE_lt S1.mem ((S0.regs 4).toNat + 0x28) 8
    rw [hs28] at this; simpa using this
  have hoR : ∀ a n, (a + n ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ a) → False ∨ True := fun _ _ _ => Or.inr trivial
  have hoA : ∀ a n, (a + n ≤ (S0.regs 4).toNat - 8 - 4128 ∨ (S0.regs 4).toNat + 16 ≤ a) →
      (a + n ≤ (S0.regs 4).toNat + 0x28 ∨ (S0.regs 4).toNat + 0x30 ≤ a) → (S0.regs 4).toNat - 8 - stack ≤ a →
      a + n ≤ (S0.regs 4).toNat + 0x78 → Outside a n (R2.rt ++ [((S0.regs 4).toNat - 8 - 4128, (S0.regs 4).toNat + 16),
        ((S0.regs 4).toNat + 0x28, (S0.regs 4).toNat + 0x30)]) := by
    intro a n h1 h2 h3 h4
    simp only [outside_append, outside_cons, outside_nil, and_true]
    exact ⟨hwR.of_sub h3 (by omega), h1, h2⟩
  have hFL : ∀ a n, (a + n ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 32 ≤ a) →
      (a + n ≤ (S0.regs 4).toNat + 0x50 ∨ (S0.regs 4).toNat + 0x6c ≤ a) → Outside a n rt → Outside a n (FL rt (S0.regs 4).toNat stack) := by
    intro a n h1 h2 h3
    simp only [FL, outside_append, outside_cons, outside_nil, and_true]
    exact ⟨h3, h1, h2⟩
  have hoRt : ∀ a n, (S0.regs 4).toNat - 8 ≤ a → a + n ≤ (S0.regs 4).toNat + 0x78 → Outside a n rt := fun a n h1 h2 =>
    hout.of_sub (by omega) (by omega)
  have hwa1 : S1.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true := by rw [mfr.accessible]; exact hwaS
  have hs58 : S1.mem.readLE ((S0.regs 4).toNat + 0x58) 8 = tab.toNat := by
    rw [mfr.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega))]; exact i58
  have hs60 : S1.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat := by
    rw [mfr.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega))]; exact i60
  have hs68 : S1.mem.readLE ((S0.regs 4).toNat + 0x68) 4 = ch.toNat % 2 ^ 32 := by
    rw [mfr.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega))]; exact i68
  have hr72 : S1.mem.readLE ((S0.regs 4).toNat + 72) 8 = S0.mem.readLE ((S0.regs 4).toNat + 72) 8 := by
    rw [mfr.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega))]
    exact ifr.readLE _ _ (hFL _ _ (by omega) (by omega) (hoRt _ _ (by omega) (by omega)))
  have hr64 : S1.mem.readLE ((S0.regs 4).toNat + 64) 8 = S0.mem.readLE ((S0.regs 4).toNat + 64) 8 := by
    rw [mfr.readLE _ _ (hoA _ _ (by omega) (by omega) (by omega) (by omega))]
    exact ifr.readLE _ _ (hFL _ _ (by omega) (by omega) (hoRt _ _ (by omega) (by omega)))
  have hBf' : ICallContract64 (Extracted.program.link impl) fmtAddr 4 stack 80 rt (fun _ => []) RBf
      (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ BigObj sc.mem P.toNat zv ∧ sc.regs 3 = tab ∧ sc.regs 1 = data ∧
        (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) := hBf
  rw [hzv] at hBO
  refine ReachesRet.mono (big_B impl R2 rt stack RBf tab data (ch.toNat % 2 ^ 32) P zv S0 S1 hBf' (Nat.mod_lt _ (by decide)) hBO hPin hAin
    hpc1 (by rw [m4, i4]) hal hwb hwn hwa1 hwR (hoRt _ _ (by omega) (by omega)) hs28 hP hs58 hs60 hs68 hr72 hr64 hret47) (fun S' h => ?_)
  obtain ⟨b4, b5, b14, bx, bfr, j0, j3, j1, hR⟩ := h
  refine ⟨b4, b5, by rw [b14, m14, i14], by rw [bx, mx, ix], ?_, P, j0, j3, j1, hR⟩
  have hSS : MemFrame S.mem S'.mem (R2.rt ++ FL rt (S0.regs 4).toNat stack ++ [((S0.regs 4).toNat + 0x28, (S0.regs 4).toNat + 0x30)]) := by
    refine mfr.trans bfr (fun a n h => ?_)
    simp only [FL, outside_append, outside_cons, outside_nil, and_true] at h ⊢
    obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := h
    exact ⟨⟨h1, by omega, h5⟩, h2, h3⟩
  refine ifr.trans hSS (fun a n h => ⟨?_, h⟩)
  have h' := h
  simp only [outside_append] at h'
  exact h'.1.2

end Fv256.Amd64.FormatBig
