import Fv256.Amd64.RecipSummary

/-!
# Transfer of the `Reciprocal` library summary to an `Ensures` statement (Extracted-free, compiled once)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.RecipSeg

namespace Fv256.Amd64.RecipEnsures

theorem ensures_recip {p : Janus.Amd64.Program} {entry : Nat}
    (hsum : Summary p entry RecPre RecSpec) (m : BitVec 64) :
    Ensures p entry [m]
      (fun s => StackGuardOK s 0x1b8 ∧ 0x248 ≤ (s.regs regSP).toNat ∧ StackWritable s 0x240 0x30 ∧ Buffer s m 32 false ∧
        Apart m.toNat 32 ((s.regs regSP).toNat - 0x240) 0x270 ∧
        Apart ((s.regs regG).toNat + 16) 8 ((s.regs regSP).toNat - 0x240) 0x270)
      (fun s s' => (valueAt s m 32 < 2 ^ 192 → s'.mem.readLE ((s.regs regSP).toNat + 8) 40 = 0) ∧
        (2 ^ 192 ≤ valueAt s m 32 → Fv256.F.RecipWeak (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        (2 ^ 193 ≤ valueAt s m 32 → Fv256.F.RecipOK (valueAt s m 32) (s'.mem.readLE ((s.regs regSP).toNat + 8) 40)) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 0x240, (s.regs regSP).toNat + 0x30)]) := by
  intro ret hret s hs ⟨hg, hsp, hw, hm, hdm, hdg⟩
  have h0 : s.regs 0 = m := hs.args 0 (by simp)
  have hrs : s.mem.readLE (s.regs 4).toNat 8 = ret := hs.ret
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_sub s.mem hw.2.2 (Or.inl rfl) (by have := hw.1; simp only [regSP] at *; omega)
      (by have := hw.1; simp only [regSP] at *; omega)
  refine Summary.returns hsum hret hs.rip (by simp only [retAddrOf, hrs]) ?_ ?_
  · simp only [regSP, regG] at *
    unfold RecPre
    rw [h0]
    exact ⟨⟨hacc, by rw [hrs]; exact hret.user⟩, hsp, hg, hw, hs.zero, hm, hdm, hdg⟩
  · intro s' ⟨e4, e5, e14, e15, hfr, h1, h2, h3⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · simp only [regSP]; first | exact e4 | (rw [e4]; rfl)
    · simp only [regFP]; first | exact e5 | (rw [e5]; rfl)
    · simp only [regG]; first | exact e14 | (rw [e14]; rfl)
    · simp only [xmmZero]; first | exact e15 | (rw [e15]; rfl)
    · simp only [valueAt, regSP]; rw [← h0]; exact h1
    · simp only [valueAt, regSP]; rw [← h0]; exact h2
    · simp only [valueAt, regSP]; rw [← h0]; exact h3
    · simp only [regSP]; exact hfr

end Fv256.Amd64.RecipEnsures
