import Fv256.SpecE

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

/-- the results of the `fmt.State` queries, as the machine sees them -/
structure Answers where
  hasWidth : Bool
  hasPrec : Bool
  flag : Nat → Bool

/-- the characters tested by the five `Flag` calls, in order: `+`, space, `-`, `0`, `#` -/
def flagChars : List Nat := [43, 32, 45, 48, 35]

/-- no width, no precision, none of the five flags -/
def Answers.plain (a : Answers) : Prop :=
  a.hasWidth = false ∧ a.hasPrec = false ∧ ∀ c ∈ flagChars, a.flag c = false

/-- the verbs of the fast path: `d`, `v`, `s`, `x` -/
def fastVerb (ch : Nat) : Prop := ch = 100 ∨ ch = 118 ∨ ch = 115 ∨ ch = 120

/-- lowercase hexadecimal digits of `n` (ASCII), most significant first, no prefix, no leading zeros; `0` is `"0"` -/
def hexBytes (n : Nat) : List Nat :=
  if h : n < 16 then [if n < 10 then 48 + n else 87 + n] else hexBytes (n / 16) ++ [if n % 16 < 10 then 48 + n % 16 else 87 + n % 16]
termination_by n
decreasing_by omega

/-- the bytes the fast path writes -/
def fastBytes (z ch : Nat) : List Nat := if ch = 120 then hexBytes z else Fv256.E.decBytes z

/-- `"<nil>"` -/
def nilText : List Nat := [60, 110, 105, 108, 62]

inductive Case | nilCase | fast | big
  deriving DecidableEq

open Classical in
/-- which case runs, from the receiver, the answers of the state and the verb -/
noncomputable def whichCase (isNil : Bool) (a : Answers) (ch : Nat) : Case :=
  if isNil then .nilCase else if a.plain ∧ fastVerb ch then .fast else .big

theorem whichCase_nil (a : Answers) (ch : Nat) : whichCase true a ch = .nilCase := by simp [whichCase]

theorem whichCase_fast (a : Answers) (ch : Nat) (h : a.plain) (hv : fastVerb ch) : whichCase false a ch = .fast := by
  simp [whichCase, h, hv]

theorem whichCase_big (a : Answers) (ch : Nat) (h : ¬ (a.plain ∧ fastVerb ch)) : whichCase false a ch = .big := by
  simp [whichCase, h]

theorem hexBytes_zero : hexBytes 0 = [48] := by simp [hexBytes]
theorem hexBytes_255 : hexBytes 255 = [102, 102] := by
  rw [hexBytes]; simp [hexBytes]

end Fv256.FormatSpec
