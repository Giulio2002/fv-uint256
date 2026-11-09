import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.SpecC
import Fv256.Spec.Format

/-!
# Specification of `(*uint256.Int).Format(s fmt.State, ch rune)` (family E), master 48f3f44

Independent of the machine.  The Go source (`conversion.go`):

```go
func (z *Int) Format(s fmt.State, ch rune) {
	if z == nil { _, _ = fmt.Fprint(s, "<nil>"); return }
	if _, hasWidth := s.Width(); !hasWidth {
		if _, hasPrec := s.Precision(); !hasPrec {
			if !s.Flag('+') && !s.Flag(' ') && !s.Flag('-') && !s.Flag('0') && !s.Flag('#') {
				switch ch {
				case 'd', 'v', 's': _, _ = s.Write([]byte(z.Dec())); return
				case 'x':           _, _ = s.Write([]byte(z.Hex()[2:])); return
				}
			}
		}
	}
	z.ToBig().Format(s, ch)
}
```

The behaviour of the `fmt.State` methods is not specified: they are interface calls into arbitrary code, so the
theorem quantifies over their results (`Answers`) and the case that runs follows from them (`whichCase`).
What `Format` guarantees, by case:

* `nil`: exactly one call of `fmt.Fprint` with the state `s` (both interface words, unchanged) and the text `"<nil>"`;
* `fast`: no width, no precision, none of the five flags, and `ch ∈ {d, v, s, x}`: exactly one `s.Write`, whose byte argument is
  `fastBytes z ch` (the decimal digits for `d`/`v`/`s`, the lowercase hexadecimal digits without `0x` for `x`);
* `big`: exactly one call of `(*big.Int).Format` with a receiver holding the value of `z` (the `ToBig` layout), and `s`, `ch` unchanged.

In every case `*z` is unchanged and memory changes only in the stack frame and the allocator's ranges.
-/

namespace Fv256.FormatSpec

/-- the results of the `fmt.State` queries, as the machine sees them: (`hasWidth`, `hasPrec`, `flag c`) (a plain tuple: the Janus audit
rejects consumer-declared structures reachable from a theorem statement) -/
abbrev Answers := Bool × Bool × (Nat → Bool)

@[reducible] def Answers.hasWidth (a : Answers) : Bool := a.1
@[reducible] def Answers.hasPrec (a : Answers) : Bool := a.2.1
@[reducible] def Answers.flag (a : Answers) : Nat → Bool := a.2.2

/-- the characters tested by the five `Flag` calls, in order: `+`, space, `-`, `0`, `#` -/
def flagChars : List Nat := [43, 32, 45, 48, 35]

/-- no width, no precision, none of the five flags -/
def Answers.plain (a : Answers) : Prop :=
  a.hasWidth = false ∧ a.hasPrec = false ∧ ∀ c ∈ flagChars, a.flag c = false

/-- the verbs of the fast path: `d`, `v`, `s`, `x` -/
def fastVerb (ch : Nat) : Prop := ch = 100 ∨ ch = 118 ∨ ch = 115 ∨ ch = 120

/-- the case tags (plain numbers, see `Answers`): `0` nil, `1` fast path, `2` through `big.Int` -/
abbrev Case := Nat
@[reducible] def Case.nilCase : Case := 0
@[reducible] def Case.fast : Case := 1
@[reducible] def Case.big : Case := 2

open Classical in
/-- which case runs, from the receiver, the answers of the state and the verb -/
noncomputable def whichCase (isNil : Bool) (a : Answers) (ch : Nat) : Case :=
  if isNil then .nilCase else if a.plain ∧ fastVerb ch then .fast else .big

theorem whichCase_nil (a : Answers) (ch : Nat) : whichCase true a ch = .nilCase := by simp [whichCase]

theorem whichCase_fast (a : Answers) (ch : Nat) (h : a.plain) (hv : fastVerb ch) : whichCase false a ch = .fast := by
  simp [whichCase, h, hv]

theorem whichCase_big (a : Answers) (ch : Nat) (h : ¬ (a.plain ∧ fastVerb ch)) : whichCase false a ch = .big := by
  simp [whichCase, h]

theorem hexBytes_digits : ∀ (n z : Nat), Fv256.C.hexDigits z n →
    hexBytes z = (List.range n).map (fun k => Fv256.C.hexChar (z / 16 ^ (n - 1 - k) % 16)) := by
  intro n
  induction n with
  | zero => intro z h; exact absurd h.1 (by omega)
  | succ n ih =>
    intro z h
    obtain ⟨h1, h2, h3⟩ := h
    by_cases hn : n = 0
    · subst hn
      have hz : z < 16 := by simpa using h2
      rw [hexBytes]; simp [hz, Fv256.C.hexChar, Nat.mod_eq_of_lt hz]
    · have hpow : 16 ^ n = 16 * 16 ^ (n - 1) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.pow_succ]; omega
      have hp1 : 1 ≤ 16 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      have h3' : 16 ^ n ≤ z := by
        rcases h3 with h3 | h3
        · omega
        · simpa using h3
      have hz : 16 ≤ z := by omega
      have hd : Fv256.C.hexDigits (z / 16) n := by
        refine ⟨by omega, ?_, Or.inr ?_⟩
        · rw [Nat.pow_succ] at h2; omega
        · omega
      rw [hexBytes, dif_neg (by omega), ih (z / 16) hd, List.range_succ, List.map_append]
      congr 1
      · apply List.map_congr_left
        intro k hk
        have hk' := List.mem_range.mp hk
        rw [Nat.div_div_eq_div_mul]
        have e : 16 * 16 ^ (n - 1 - k) = 16 ^ (n + 1 - 1 - k) := by
          obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
          have e1 : n - 1 - k = j := by omega
          have e2 : n + 1 - 1 - k = j + 1 := by omega
          rw [e1, e2, Nat.pow_succ]; omega
        rw [e]
      · simp [Fv256.C.hexChar]

theorem hexBytes_zero : hexBytes 0 = [48] := by simp [hexBytes]
theorem hexBytes_255 : hexBytes 255 = [102, 102] := by
  rw [hexBytes]; simp [hexBytes]

end Fv256.FormatSpec
