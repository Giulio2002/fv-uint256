import Fv256.Proofs.Amd64.RecipArith2
open Fv256.Amd64.RecipSeg
set_option maxRecDepth 100000
theorem sbb4 (x7aerax x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x7aem98 x7aema0 x7aema8 x801rdx x801rbx x801m50 x801m48 x801m40 : Nat)
  (b0 : x7aerax < 2^64) (b1 : x7aerdx < 2^64) (b2 : x7aerbx < 2^64) (b3 : x7aersi < 2^64) (b4 : x7aerdi < 2^64) (b5 : x7aer8 < 2^64) (b6 : x7aer11 < 2^64)
  (b7 : x7aem98 < 2^64) (b8 : x7aema0 < 2^64) (b9 : x7aema8 < 2^64)
  (h_x801rdx : x801rdx = (0 % 18446744073709551616 + 18446744073709551616 - x7aerbx % 18446744073709551616 - (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat) % 18446744073709551616)
  (h_x801rbx : x801rbx = (0 % 18446744073709551616 + 18446744073709551616 - x7aer8 % 18446744073709551616 - (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat) % 18446744073709551616)
  (h_x801m40 : x801m40 = (x7aema8 % 18446744073709551616 + 18446744073709551616 - x7aerdi % 18446744073709551616 - (1 - (x7aem98 + (18446744073709551616 - x7aersi - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616))) / 18446744073709551616)) % 18446744073709551616)
  (h_x801m48 : x801m48 = (x7aem98 % 18446744073709551616 + 18446744073709551616 - x7aersi % 18446744073709551616 - (1 - (x7aema0 + (18446744073709551616 - x7aerax - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat)) / 18446744073709551616)) % 18446744073709551616)
  (h_x801m50 : x801m50 = (x7aema0 % 18446744073709551616 + 18446744073709551616 - x7aerax % 18446744073709551616 - (decide (0 < x7aer8 + (decide (0 < x7aerbx + (decide (0 < x7aer11 + (decide (0 < x7aerdx)).toNat)).toNat)).toNat)).toNat) % 18446744073709551616)
  : x801rdx + 2^64 * x801rbx + 2^128 * x801m50 + 2^192 * x801m48 + 2^256 * x801m40
     = ((x7aema0 + 2^64 * x7aem98 + 2^128 * x7aema8) * 2^256 + 2^448 - (x7aerdx + 2^64 * x7aer11 + 2^128 * x7aerbx + 2^192 * x7aer8 + 2^256 * x7aerax + 2^320 * x7aersi + 2^384 * x7aerdi)) % 2^448 / 2^128 := by
  simp (disch := omega) only [pos_toNat] at h_x801rdx h_x801rbx h_x801m50 h_x801m48 h_x801m40
  subst h_x801rdx h_x801rbx h_x801m50 h_x801m48 h_x801m40
  janus_carry
