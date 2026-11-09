import Fv256.Proofs.Arm64.ErlpDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the memory facts at the return of `newobject` on the multi-byte path (`Mw`), from the frames -/
theorem erlp_s1m (rt : List (Nat × Nat)) (m0 M0 Mw : Memory) (sp stack z tab w rbp ret bl fn : Nat)
    (h4104 : 4104 ≤ stack) (hwb : 64 + stack ≤ sp)
    (hout : Outside (sp - 64 - stack) (stack + 96) rt) (htr : Outside (tab + 24) 8 rt)
    (hzo : Outside z 32 rt) (hzd : z + 32 ≤ sp - 64 - stack ∨ sp - 64 - stack + (stack + 96) ≤ z)
    (htd : tab + 24 + 8 ≤ sp - 64 - stack ∨ sp - 64 - stack + (stack + 96) ≤ tab + 24) (hbl : bl ≤ 256)
    (hwa : m0.accessible (sp - (64 + stack)) (64 + stack + 32) true = true)
    (hta : m0.accessible (tab + 24) 8 false = true) (hfn' : m0.readLE (tab + 24) 8 = fn)
    (hz64 : z < 2 ^ 64) (hrbp : rbp < 2 ^ 64) (htab : tab < 2 ^ 64) (hw64 : w < 2 ^ 64)
    (hfr : MemFrame m0 M0 [(sp - 72, sp - 56), (sp + 16, sp + 32)])
    (m72 : M0.readLE (sp - 72) 8 = rbp) (m64 : M0.readLE (sp - 64) 8 = ret)
    (m16 : M0.readLE (sp + 16) 8 = tab) (m24 : M0.readLE (sp + 24) 8 = w)
    (hfm : MemFrame ((M0.writeLE (sp + 8) 8 z).writeLE (sp - 16) 8 bl) Mw
      (rt ++ [(sp - 64 - 4096, sp - 64 - 8), (sp - 64 + 8, sp - 64 + 8 + 8)])) :
    Mw.readLE (sp - 72) 8 = rbp ∧ Mw.readLE (sp - 64) 8 = ret ∧ Mw.readLE (sp + 8) 8 = z ∧ Mw.readLE (sp - 16) 8 = bl ∧
    Mw.readLE (sp + 16) 8 = tab ∧ Mw.readLE (sp + 24) 8 = w ∧
    (∀ a n, z ≤ a → a + n ≤ z + 32 → Mw.readLE a n = m0.readLE a n ∧ Mw.accessible a n false = m0.accessible a n false) ∧
    Mw.readLE (tab + 24) 8 = fn ∧ Mw.accessible (tab + 24) 8 false = true ∧
    Mw.accessible (sp - (64 + stack)) (64 + stack + 32) true = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfm.readLE (sp - 72) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inl (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m72
  · rw [hfm.readLE (sp - 64) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inl (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m64
  · rw [hfm.readLE (sp + 8) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    omega
  · rw [hfm.readLE (sp - 16) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    omega
  · rw [hfm.readLE (sp + 16) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m16
  · rw [hfm.readLE (sp + 24) 8 (out_win hout h4104 hwb (by omega) (by omega) (Or.inr (by omega)))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m24
  · intro a n h1 h2
    refine ⟨?_, ?_⟩
    · rw [hfm.readLE a n (out_z hzo hzd h4104 hwb h1 h2)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact hfr.readLE a n (out_z2 hzd h4104 hwb h1 h2)
    · rw [hfm.accessible]
      simp only [Janus.Arm64.Memory.accessible_writeLE]
      exact hfr.accessible a n false
  · rw [hfm.readLE _ _ (by
      simp only [outside_append, outside_cons, outside_nil]
      refine ⟨htr, ?_, ?_, trivial⟩ <;> omega)]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)]
    exact hfn'
  · rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    exact hta
  · rw [hfm.accessible]
    simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible]
    exact hwa

end Fv256.Arm64.EncodeRLP
