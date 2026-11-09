

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


namespace Fv256.I

/-- ASCII decimal digit. -/
def isDec (c : Nat) : Prop := 48 ≤ c ∧ c ≤ 57

/-- positional value (base 10, most significant first) of the `n` bytes `b a, ..., b (a+n-1)` (a non-digit counts `0`). -/
def decSum (b : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => decSum b a n * 10 + (b (a + n) - 48)

/-- every byte of `[a, c)` is an ASCII digit. -/
def allDec (b : Nat → Nat) (a c : Nat) : Prop := ∀ k, a ≤ k → k < c → isDec (b k)

/-- the offset after at most one leading `+`. -/
def plusEnd (b : Nat → Nat) (n : Nat) : Nat := if 0 < n ∧ b 0 = 43 then 1 else 0

/-- the number of consecutive `'0'` bytes of `b` starting at `a`, below `n` (fuel `f`). -/
def zerosFrom (b : Nat → Nat) (n : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, a => if a < n ∧ b a = 48 then zerosFrom b n f (a + 1) + 1 else 0

/-- the start of the number after the leading `+` and the leading zeros are dropped; an all-zero string keeps one
`'0'` (so that `"000"` parses as `0`, not as the empty string). -/
def startPos (b : Nat → Nat) (n : Nat) : Nat :=
  if plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n) = n ∧ plusEnd b n < n then n - 1
  else plusEnd b n + zerosFrom b n (n - plusEnd b n) (plusEnd b n)

/-- the 19-character chunk of round `i` (counted from the least significant end `n`) of the number starting at `p`:
`[lo, hi)`. -/
def chunkBounds (n p i : Nat) : Nat × Nat :=
  (if p + 19 ≤ n - 19 * i then n - 19 * i - 19 else p, n - 19 * i)

open Classical in
/-- the first (least significant) chunk that has a non-digit, as `(lo, len)`. -/
noncomputable def firstBad (b : Nat → Nat) (n p : Nat) : Nat → Nat → Option (Nat × Nat)
  | 0, _ => none
  | f + 1, i =>
    if n - p ≤ 19 * i then none
    else if allDec b (chunkBounds n p i).1 (chunkBounds n p i).2 then firstBad b n p f (i + 1)
    else some ((chunkBounds n p i).1, (chunkBounds n p i).2 - (chunkBounds n p i).1)

/-- the outcome of `SetFromDecimal`: the number, `io.EOF`, `ErrBig256Range`, or the `strconv` syntax error of the
chunk `[lo, lo+len)` of the original string. -/
abbrev Res : Type := Nat × Nat × Nat

/-- the number `v` -/
@[match_pattern] def Res.ok (v : Nat) : Res := (0, v, 0)

/-- `io.EOF` -/
@[match_pattern] def Res.eof : Res := (1, 0, 0)

/-- `ErrBig256Range` -/
@[match_pattern] def Res.range : Res := (2, 0, 0)

/-- the `strconv` syntax error of the chunk `[lo, lo+len)` -/
@[match_pattern] def Res.syntax (lo len : Nat) : Res := (3, lo, len)

open Classical in
/-- parse the stripped digit string `[p, n)` (at most 78 digits). -/
noncomputable def fromDec (b : Nat → Nat) (n p : Nat) : Res :=
  if n ≤ p then .eof
  else match firstBad b n p 5 0 with
    | some (lo, len) => .syntax lo len
    | none => .ok (decSum b p (n - p))

/-- the decimal digits of `2^256 - 1` (78 of them), as ASCII codes. -/
def maxDigit (k : Nat) : Nat := (2 ^ 256 - 1) / 10 ^ (77 - k) % 10 + 48

/-- bytewise lexicographic `x > y` on the first `n` bytes. -/
def lexGt (x y : Nat → Nat) (n : Nat) : Prop := ∃ k, k < n ∧ (∀ j, j < k → x j = y j) ∧ y k < x k

open Classical in
/-- `SetFromDecimal(s)` for the string whose bytes are `b 0, ..., b (n-1)`. -/
noncomputable def decParse (b : Nat → Nat) (n : Nat) : Res :=
  if n - startPos b n < 78 then fromDec b n (startPos b n)
  else if n - startPos b n = 78 then
    (if lexGt (fun k => b (startPos b n + k)) maxDigit 78 then .range else fromDec b n (startPos b n))
  else .range
