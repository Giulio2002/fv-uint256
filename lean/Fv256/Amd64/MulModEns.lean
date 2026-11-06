import Janus
import Fv256.Spec
import Fv256.SpecF
import Fv256.Util

/-!
# Transfer of the `MulMod` / `MulModWithReciprocal` library summaries to `Ensures` statements (Extracted-free)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.MulModEns

/-- the library-summary precondition of `MulMod` (receiver `RAX`, `x` `RBX`, `y` `RCX`, `m` `RDI`) -/
abbrev MmPre (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  0x380 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x2f0 ∧ StackWritable s 0x378 0x28 ∧ s.xmm 15 = 0 ∧
  Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 32 false ∧
  Apart (s.regs 0).toNat 32 ((s.regs 4).toNat - 0x378) 0x3a0 ∧
  Apart (s.regs 3).toNat 32 ((s.regs 4).toNat - 0x378) 0x3a0 ∧
  Apart (s.regs 1).toNat 32 ((s.regs 4).toNat - 0x378) 0x3a0 ∧
  Apart (s.regs 7).toNat 32 ((s.regs 4).toNat - 0x378) 0x3a0 ∧
  Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 0x378) 0x3a0

abbrev MmPost (s s' : State) : Prop :=
  s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
  s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.mulmodSpec (s.mem.readLE (s.regs 3).toNat 32)
    (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 32) ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x378, (s.regs 4).toNat),
    ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x28)]

theorem ensures_mm {p : Janus.Amd64.Program} {entry : Nat} (hsum : Summary p entry MmPre MmPost) (z x y m : BitVec 64) :
    Ensures p entry [z, x, y, m]
      (fun s => StackGuardOK s 0x2f0 ∧ 0x380 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x378 0x28 ∧
        Buffer s z 32 true ∧ Buffer s x 32 false ∧ Buffer s y 32 false ∧ Buffer s m 32 false ∧
        Apart z.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart x.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart y.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart m.toNat 32 (((s.regs regSP).toNat) - 0x378) 0x3a0 ∧
        Apart ((s.regs regG).toNat + 16) 8 (((s.regs regSP).toNat) - 0x378) 0x3a0)
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Fv256.F.mulmodSpec (valueAt s x 32) (valueAt s y 32) (valueAt s m 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - 0x378, (s.regs regSP).toNat),
          ((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 0x28)]) := by
  intro ret hret s hs ⟨hg, hsp, hw, hz, hx, hy, hm, hdz, hdx, hdy, hdm, hdg⟩
  have h0 : s.regs 0 = z := hs.args 0 (by simp)
  have h3 : s.regs 3 = x := hs.args 1 (by simp)
  have h1 : s.regs 1 = y := hs.args 2 (by simp)
  have h7 : s.regs 7 = m := hs.args 3 (by simp)
  have hrs : s.mem.readLE (s.regs 4).toNat 8 = ret := hs.ret
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub s.mem hw.2.2 (Or.inl rfl) (by have := hw.1; simp only [regSP] at *; omega)
      (by have := hw.1; simp only [regSP] at *; omega)
  refine Summary.returns hsum hret hs.rip (by simp only [retAddrOf, hrs]) ?_ ?_
  · unfold MmPre
    simp only [regSP, regG] at *
    rw [h0, h3, h1, h7]
    exact ⟨⟨hacc, by rw [hrs]; exact hret.user⟩, hsp, hg, hw, hs.zero, hz, hx, hy, hm, hdz, hdx, hdy, hdm, hdg⟩
  · intro s' ⟨e0, e4, e5, e14, e15, edf, emx, hv, hf⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp only [regSP]; rw [e4]
    · simp only [regFP]; rw [e5]
    · simp only [regG]; rw [e14]
    · simp only [xmmZero]; rw [e15]
    · rw [e0, h0]
    · simp only [valueAt]; rw [← h0, ← h3, ← h1, ← h7]; exact hv
    · simp only [regSP]; rw [← h0]; exact hf

end Fv256.Amd64.MulModEns
