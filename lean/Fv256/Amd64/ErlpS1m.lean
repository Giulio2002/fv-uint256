import Fv256.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the memory facts at the return of `newobject` on the multi-byte path (`Mw`), from the frames; `m0` is the call state's memory,
`M0` the memory at the join, `Mw` the memory the allocator returns -/
theorem erlp_s1m (rt : List (Nat × Nat)) (m0 M0 Mw : Memory) (rsp stack z tab w rbp ret bl fn : Nat)
    (h4104 : 4104 ≤ stack) (hwb : 56 + stack ≤ rsp)
    (hout : Outside (rsp - 56 - stack) (stack + 88) rt) (htr : Outside (tab + 24) 8 rt)
    (hzo : Outside z 32 rt) (hzd : z + 32 ≤ rsp - 56 - stack ∨ rsp + 32 ≤ z)
    (htd : tab + 32 ≤ rsp - 56 - stack ∨ rsp + 32 ≤ tab + 24) (hbl : bl ≤ 256)
    (hza : m0.accessible z 32 false = true) (hwa : m0.accessible (rsp - (56 + stack)) (56 + stack + 32) true = true)
    (hta : m0.accessible (tab + 24) 8 false = true) (hfn' : m0.readLE (tab + 24) 8 = fn) (hr : m0.readLE rsp 8 = ret)
    (hz64 : z < 2 ^ 64) (hrbp : rbp < 2 ^ 64) (htab : tab < 2 ^ 64) (hw64 : w < 2 ^ 64)
    (hfr : MemFrame m0 M0 [(rsp - 8, rsp), (rsp + 16, rsp + 32)])
    (m8 : M0.readLE (rsp - 8) 8 = rbp) (m16 : M0.readLE (rsp + 16) 8 = tab) (m24 : M0.readLE (rsp + 24) 8 = w)
    (retv : Nat)
    (hfm : MemFrame (((M0.writeLE (rsp + 8) 8 z).writeLE (rsp - 16) 8 bl).writeLE (rsp - 56) 8 retv) Mw
      (rt ++ [(rsp - 56 - 4096, rsp - 56), (rsp - 56 + 8, rsp - 56 + 8 + 8)])) :
    Mw.readLE (rsp - 8) 8 = rbp ∧ Mw.readLE rsp 8 = ret ∧ Mw.readLE (rsp + 8) 8 = z ∧ Mw.readLE (rsp - 16) 8 = bl ∧
    Mw.readLE (rsp + 16) 8 = tab ∧ Mw.readLE (rsp + 24) 8 = w ∧
    (∀ a n, z ≤ a → a + n ≤ z + 32 → Mw.readLE a n = m0.readLE a n ∧ Mw.accessible a n false = m0.accessible a n false) ∧
    Mw.readLE (tab + 24) 8 = fn ∧ Mw.accessible (tab + 24) 8 false = true ∧
    Mw.accessible (rsp - (56 + stack)) (56 + stack + 32) true = true := by
  have hc1 : ∀ a n, rsp - 40 ≤ a → a + n ≤ rsp + 32 → Outside a n (rt ++ [(rsp - 56 - 4096, rsp - 56), (rsp - 56 + 8, rsp - 56 + 8 + 8)]) :=
    fun a n h1 h2 => out_win hout h4104 hwb h1 h2
  have hc1 : ∀ a n, rsp - 40 ≤ a → a + n ≤ rsp + 32 → Outside a n (rt ++ [(rsp - 56 - 4096, rsp - 56), (rsp - 56 + 8, rsp - 56 + 8 + 8)]) :=
    fun a n h1 h2 => out_win hout h4104 hwb h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfm.readLE (rsp - 8) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m8
  · rw [hfm.readLE (rsp) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    rw [hfr.readLE _ _ (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)]
    exact hr
  · rw [hfm.readLE (rsp + 8) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    omega
  · rw [hfm.readLE (rsp - 16) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    omega
  · rw [hfm.readLE (rsp + 16) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m16
  · rw [hfm.readLE (rsp + 24) 8 (hc1 _ _ (by omega) (by omega))]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact m24
  · intro a n h1 h2
    refine ⟨?_, ?_⟩
    · rw [hfm.readLE a n (out_z hzo hzd h4104 hwb h1 h2)]
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact hfr.readLE a n (out_z2 hzd hwb h1 h2)
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

end Fv256.Amd64.EncodeRLP
