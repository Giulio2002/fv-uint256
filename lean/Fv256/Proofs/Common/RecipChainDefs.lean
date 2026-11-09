import Fv256.Proofs.Common.RecipStages

/-!
# `Reciprocal`: the pure-Nat model of the library code (Extracted-free)

`y = m * 2^s` is the normalised 256-bit value (`s = clz` of the top limb of `m`); every `recipRk y` is the closed form of the
value the k-th stage of the machine code leaves behind.
-/

namespace Fv256.F
open Fv256.RecipMath

/-- the `i`-th 64-bit word of `y` -/
def yw (y i : Nat) : Nat := y / 2 ^ (64 * i) % 2 ^ 64

/-- the `i`-th word of `R²` -/
def rsqw (R i : Nat) : Nat := R * R / 2 ^ (64 * i) % 2 ^ 64

def recipS (m : Nat) : Nat := 255 - Nat.log2 m
def recipY (m : Nat) : Nat := m * 2 ^ recipS m

/-- first approximation `r0` (a 32-bit value) -/
def recipR0 (y : Nat) : Nat :=
  if yw y 3 / 2 ^ 32 = 2 ^ 31 then 2 ^ 32 - 1 else 2 ^ 63 / (yw y 3 / 2 ^ 32)

def recipT1 (y : Nat) : Nat := (recipR0 y * recipR0 y % 2 ^ 64) * yw y 3 / 2 ^ 64

def recipR1raw (y : Nat) : Nat := 2 * ((recipR0 y * 2 ^ 32 + 2 ^ 64 - recipT1 y) % 2 ^ 64) % 2 ^ 64

/-- stage 1: `r1` after the `cmove` -/
def recipR1 (y : Nat) : Nat :=
  if (recipR1raw y ||| 2 * yw y 3 % 2 ^ 64) = 0 then 2 ^ 64 - 1 else recipR1raw y

def recipR2raw (y : Nat) : Nat :=
  (2 * (recipR1 y * 2 ^ 64) + 2 ^ 128 - (2 * stage2e (recipR1 y) (yw y 2) (yw y 3)) % 2 ^ 128) % 2 ^ 128

/-- stage 2 (128 bit) -/
def recipR2 (y : Nat) : Nat :=
  if recipR2raw y = 0 ∧ 2 * yw y 3 % 2 ^ 64 = 0 then 2 ^ 128 - 1 else recipR2raw y

def recipQ3 (y : Nat) : Nat :=
  stage3q (rsqw (recipR2 y) 0) (rsqw (recipR2 y) 1) (rsqw (recipR2 y) 2) (rsqw (recipR2 y) 3)
    (yw y 0) (yw y 1) (yw y 2) (yw y 3)

/-- stage 3 (192 bit) -/
def recipR3 (y : Nat) : Nat :=
  2 * (((recipR2 y * 2 ^ 192 + 2 ^ 320 - recipQ3 y) % 2 ^ 320) / 2 ^ 128) % 2 ^ 192

/-- the sum of the products `w_i y_j 2^(64 (i+j-3))`, `i + j ≥ 3`, of `R3²` with `y` -/
def recipV4 (y : Nat) : Nat :=
  2 ^ 0 * (rsqw (recipR3 y) 0 * yw y 3 + rsqw (recipR3 y) 1 * yw y 2 + rsqw (recipR3 y) 2 * yw y 1 + rsqw (recipR3 y) 3 * yw y 0) +
  2 ^ 64 * (rsqw (recipR3 y) 1 * yw y 3 + rsqw (recipR3 y) 2 * yw y 2 + rsqw (recipR3 y) 3 * yw y 1 + rsqw (recipR3 y) 4 * yw y 0) +
  2 ^ 128 * (rsqw (recipR3 y) 2 * yw y 3 + rsqw (recipR3 y) 3 * yw y 2 + rsqw (recipR3 y) 4 * yw y 1 + rsqw (recipR3 y) 5 * yw y 0) +
  2 ^ 192 * (rsqw (recipR3 y) 3 * yw y 3 + rsqw (recipR3 y) 4 * yw y 2 + rsqw (recipR3 y) 5 * yw y 1) +
  2 ^ 256 * (rsqw (recipR3 y) 4 * yw y 3 + rsqw (recipR3 y) 5 * yw y 2) +
  2 ^ 320 * (rsqw (recipR3 y) 5 * yw y 3)

/-- stage 4 (320 bit) -/
def recipR4pre (y : Nat) : Nat := (recipR3 y * 2 ^ 256 + 2 ^ 448 - recipV4 y) % 2 ^ 448 / 2 ^ 128

/-- stage 5: the final decrement -/
def recipR4 (y : Nat) : Nat :=
  if 2 ^ 574 < recipR4pre y * y then (recipR4pre y + 2 ^ 320 - 1) % 2 ^ 320 else recipR4pre y

def recipTail (s r4 : Nat) : Nat := if s ≤ 62 then r4 / 2 ^ (62 - s) else 2 * r4 % 2 ^ 320

def recipPow2 (m : Nat) : Nat := 2 ^ 256 - 1 + 2 ^ 256 * ((2 ^ 64 - 1) / 2 ^ (Nat.log2 m % 64))

def recipModel (m : Nat) : Nat :=
  if m < 2 ^ 192 then 0
  else if m = 2 ^ Nat.log2 m then recipPow2 m
  else recipTail (recipS m) (recipR4 (recipY m))

theorem recip_lt192 (m : Nat) (h : m < 2 ^ 192) : recipModel m = 0 := by
  unfold recipModel; simp [h]

end Fv256.F
