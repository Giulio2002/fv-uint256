import Janus

/-!
# Transfer of a two-pointer library summary with an output relation to an `Ensures` statement

`ensures2s`: a library `Summary` (receiver `RAX`, operand `RBX`, result related to the operand by `R` at the receiver, window
`[RSP-b, RSP+u)`, `z` and `x` equal or disjoint: the shape of the `Sqrt` summary) gives the `Ensures` statement of the function, over
the same program.  It does not mention `Extracted`, so it is compiled once.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.EnsuresOfS

theorem ensures2s {p : Janus.Amd64.Program} {entry : Nat} (lo b g u : Nat) (hu : 8 ≤ u) (R : Nat → Nat → Prop)
    (hsum : Summary p entry
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        lo ≤ (s.regs 4).toNat ∧ StackGuardOK s g ∧ StackWritable s b u ∧ s.xmm 15 = 0 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - b ∨ (s.regs 4).toNat + u ≤ (s.regs 0).toNat) ∧
        ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - b ∨ (s.regs 4).toNat + u ≤ (s.regs 3).toNat) ∧
        (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - b ∨ (s.regs 4).toNat + u ≤ (s.regs 14).toNat + 16))
      (fun s s' => s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
        R (s.mem.readLE (s.regs 3).toNat 32) (s'.mem.readLE (s.regs 0).toNat 32) ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - b, (s.regs 4).toNat + u)]))
    (z x : BitVec 64) :
    Ensures p entry [z, x]
      (fun s => StackGuardOK s g ∧ lo ≤ (s.regs regSP).toNat ∧ StackWritable s b u ∧ Buffer s z 32 true ∧
        Buffer s x 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - b ∨ (s.regs regSP).toNat + u ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - b ∨ (s.regs regSP).toNat + u ≤ x.toNat) ∧
        (z = x ∨ z.toNat + 32 ≤ x.toNat ∨ x.toNat + 32 ≤ z.toNat) ∧
        ((s.regs regG).toNat + 24 ≤ (s.regs regSP).toNat - b ∨ (s.regs regSP).toNat + u ≤ (s.regs regG).toNat + 16))
      (fun s s' => s'.regs 0 = z ∧ R (valueAt s x 32) (valueAt s' z 32) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs regSP).toNat - b, (s.regs regSP).toNat + u)]) := by
  intro ret hret s hs ⟨hg, hsp, hw, hz, hx, hdz, hdx, hzx, hdg⟩
  have h0 : s.regs 0 = z := hs.args 0 (by simp)
  have h3 : s.regs 3 = x := hs.args 1 (by simp)
  have hrs : s.mem.readLE (s.regs 4).toNat 8 = ret := hs.ret
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub s.mem hw.2.2 (Or.inl rfl) (by have := hw.1; simp only [regSP] at *; omega)
      (by have := hw.1; simp only [regSP] at *; omega)
  refine Summary.returns hsum hret hs.rip (by simp only [retAddrOf, hrs]) ?_ ?_
  · simp only [regSP, regG] at *
    rw [h0, h3]
    exact ⟨⟨hacc, by rw [hrs]; exact hret.user⟩, hsp, hg, hw, hs.zero, hz, hx, hdz, hdx, hzx, hdg⟩
  · intro s' ⟨e0, e4, e5, e14, e15, edf, emx, hv, hf⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp only [regSP]; rw [e4]
    · simp only [regFP]; rw [e5]
    · simp only [regG]; rw [e14]
    · simp only [xmmZero]; rw [e15]
    · rw [e0, h0]
    · simp only [valueAt]; rw [← h0, ← h3]; exact hv
    · simp only [regSP]; rw [← h0]; exact hf

end Fv256.Amd64.EnsuresOfS
