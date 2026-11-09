import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SpecI
import Fv256.Proofs.Common.UtilI
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.SfdEnvC

/-!
# `UnmarshalText` / `UnmarshalJSON` (arm64): precondition and the `SetFromDecimal` call-site lemma (Extracted-free)

`string(input)` is `runtime.slicebytetostring(buf, ptr, n)` (a live runtime contract).  `PreU` is the entry precondition
(the model facts of `SfdTopSpec.TopPre` for the receiver `z`, the input slice, the contract's own model facts);
`toppre_dec` builds `TopPre` for the `SetFromDecimal` call from the state after the copy.

Frame of `UnmarshalText` (entry `SP = sp0`, 16-aligned): `SP1 = sp0 - 112`; `[SP1]` = saved `X30`, `[sp0 - 120]` = saved `X29`;
spills `[sp0 + 8]` = `z`, `[sp0 + 16]` = `ptr`; hex buffer `[sp0 - 72, sp0 - 40)`, decimal buffer `[sp0 - 40, sp0 - 8)`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec

namespace Fv256.Arm64.UnmarshalSpec

variable (C : SfdCfg)

/-- Package-initialisation facts about the sentinel error variables (documented environment assumption: `io.EOF` and
`uint256.ErrBig256Range` are initialised interface values) and the well-formedness of the interface model's private ranges. -/
def InitDone (R2 : IfaceModel) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE C.ioEOF 8 ≠ 0 ∧ m.readLE (C.ioEOF + 8) 8 ≠ 0 ∧ m.readLE C.errBig 8 ≠ 0 ∧ m.readLE (C.errBig + 8) 8 ≠ 0 ∧
  (∀ r ∈ R2.priv, r.1 ≤ r.2)

theorem outside_of_in {rt : List (Nat × Nat)} {z n : Nat} (hz : InRanges z n rt) :
    ∀ rs : List (Nat × Nat), (∀ r ∈ rs, r.1 ≤ r.2) → (∀ r ∈ rs, Outside r.1 (r.2 - r.1) rt) → Outside z n rs := by
  intro rs
  induction rs with
  | nil => intros; trivial
  | cons r rs ih =>
    intro hw ho
    obtain ⟨a, b⟩ := r
    simp only [outside_cons]
    refine ⟨?_, ih (fun r hr => hw r (List.mem_cons_of_mem _ hr)) (fun r hr => ho r (List.mem_cons_of_mem _ hr))⟩
    obtain ⟨q, hq, h1, h2⟩ := hz
    have hab := hw (a, b) (List.mem_cons_self ..)
    have := MemFrame.outside_mem (ho (a, b) (List.mem_cons_self ..)) hq
    simp only at hab this
    omega

/-! `Mod` accessors: the only place that destructures `Mod` (so a change of `Mod` is a one-place edit). -/
theorem Mod.laws {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) : R2.Laws := by
  obtain ⟨m1, -⟩ := h; exact m1

theorem Mod.priv {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ R2.priv, Outside r.1 (r.2 - r.1) R.rt := by
  obtain ⟨m1, m2, m3, m4, m5, -⟩ := h; exact m5

theorem Mod.lpriv {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ L, Outside r.1 (r.2 - r.1) R2.priv := by
  obtain ⟨m1, m2, m3, m4, m5, m6, -⟩ := h; exact m6

theorem Mod.static {R : RtInv} {R2 : IfaceModel} {T : Nat} {L : List (Nat × Nat)} (h : Mod C R R2 T L) :
    ∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) R.rt := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, -⟩ := h; exact m8

theorem Mod.extL {R : RtInv} {R2 : IfaceModel} {T : Nat} {L L' : List (Nat × Nat)} (h : Mod C R R2 T L)
    (h' : ∀ r ∈ L', Outside r.1 (r.2 - r.1) R2.priv) : Mod C R R2 T L' := by
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ := h
  exact ⟨m1, m2, m3, m4, m5, h', m7, m8, m9, m10, m11, m12, m13⟩

/-- entry precondition of `UnmarshalText`/`UnmarshalJSON`: receiver `z` in `X0`, input slice `(pI, nI)` in `X1`/`X2`.
`[lo, hi)` is the absolute stack window.  `sb` is the address of `runtime.slicebytetostring`, `st` that of `runtime.staticuint64s`. -/
