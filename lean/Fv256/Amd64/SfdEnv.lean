import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SumC64

/-!
# Static runtime-model facts for `SetFromDecimal`'s error paths (amd64)

`StaticOK R2 T m`: the facts about the binary's static data that the `strconv.toError` proof reads, stated about a
memory `m`: the `internal/strconv.Error` itab and its type descriptor `T` (regular memory, not a direct interface,
size 8, a descriptor of the interface model `R2`), the `strconv.NumError` type descriptor bytes (`Size_ = 48`, has
pointers), and the readability of the write-barrier flag, `strconv.ErrSyntax` and the itab / constant objects.
`StaticOK.frame`: it survives any `MemFrame` whose ranges avoid `staticRanges T`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type

namespace Fv256.Amd64.SfdEnv

abbrev numErrType : Nat := Extracted.dataAddr.«type:strconv.NumError#3eb4e62e»
abbrev numErrItab : Nat := Extracted.dataAddr.«go:itab.*strconv.NumError,error»
abbrev errItab : Nat := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»
abbrev synConst : Nat := Extracted.dataAddr.«.rodata#9967e7a3»
abbrev strconvErrSyntax : Nat := Extracted.dataAddr.«strconv.ErrSyntax»
abbrev wbFlag : Nat := Extracted.dataAddr.«runtime.writeBarrier»

/-- the ranges `[lo, hi)` the static facts read (the descriptor `T` has `typeDescSize = 48` bytes). -/
def staticRanges (T : Nat) : List (Nat × Nat) :=
  [(errItab, errItab + 16), (synConst, synConst + 8), (strconvErrSyntax, strconvErrSyntax + 16), (wbFlag, wbFlag + 4),
    (numErrType, numErrType + 16), (T, T + 48)]

def StaticOK (R2 : IfaceModel) (T : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE (errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory m T = true ∧ isDirectIface m T = false ∧
  tySize m T = 8 ∧ m.readLE numErrType 8 = 48 ∧ m.readLE (numErrType + 8) 8 ≠ 0 ∧
  m.accessible wbFlag 4 false = true ∧ m.accessible strconvErrSyntax 16 false = true ∧
  m.accessible errItab 16 false = true ∧ m.accessible synConst 8 false = true

theorem StaticOK.frame {R2 : IfaceModel} {T : Nat} {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h : StaticOK R2 T m) (hf : MemFrame m m' ws)
    (ho : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) ws) : StaticOK R2 T m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have oI := ho (errItab, errItab + 16) (by simp [staticRanges])
  have oS := ho (synConst, synConst + 8) (by simp [staticRanges])
  have oE := ho (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  have oW := ho (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have oN := ho (numErrType, numErrType + 16) (by simp [staticRanges])
  have oT := ho (T, T + 48) (by simp [staticRanges])
  simp only [Nat.add_sub_cancel_left] at oI oS oE oW oN oT
  refine ⟨?_, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.readLE _ _ (Outside.of_sub oI (by omega) (by omega))]; exact h1
  · simp only [isRegularMemory, tyTFlag] at h3 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h3
  · simp only [isDirectIface, tyTFlag] at h4 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h4
  · simp only [tySize] at h5 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h5
  · rw [hf.readLE _ _ (Outside.of_sub oN (by omega) (by omega))]; exact h6
  · rw [hf.readLE _ _ (Outside.of_sub oN (by omega) (by omega))]; exact h7
  · rw [hf.accessible]; exact h8
  · rw [hf.accessible]; exact h9
  · rw [hf.accessible]; exact h10
  · rw [hf.accessible]; exact h11

end Fv256.Amd64.SfdEnv
