import Janus
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util

/-!
# `(*uint256.Int).Hex`: ISA-independent specification pieces (shared by the arm64 and amd64 proofs)

`HexQ v s s'`: the call returns a string whose bytes are `hexStrBytes v n` ("0x" followed by the `n` hexadecimal digits of `v`,
most significant first, no leading zeros, `v = 0` gives "0x0") for the number of digits `n` of `v` (`hexDigits v n`).
`hex_strbytes`: the bytes of the cropped buffer (digits at `A+2+p`, then `0x` written in front) are exactly `hexStrBytes`.
-/

open Janus Janus.Arm64 Janus.Spec Janus.Contracts Fv256.C

namespace Fv256.Hex

/-- the digit at nibble position `p` (counted from the most significant of 64) of `v` -/
def dig (v p : Nat) : Nat := v / 16 ^ (63 - p) % 16

/-- the string at `[p, p+len)` of memory `m` is the hexadecimal rendering of `v` (ISA independent) -/
def HexOut (v : Nat) (m : Memory) (p len : Nat) : Prop :=
  ∃ n, hexDigits v n ∧ StrOut m p len (hexStrBytes v n)

/-- the postcondition of `Hex` for the value `v` on arm64 (result string in `X0`, `X1`) -/
def HexQ (_rt : List (Nat × Nat)) (v : Nat) (_s s' : State) : Prop :=
  HexOut v s'.mem (s'.regs 0).toNat (s'.regs 1).toNat

theorem fin_strout (w2 m0 : Memory) (w8 w7 : BitVec 64) (m1 : Memory) (p n : Nat) (bs : List Nat) (hl : bs.length = n)
    (hacc : ∀ a n, w2.accessible a n false = m0.accessible a n false)
    (h : w7.toNat = (strBytes m1 p n).length ∧ w8.toNat + w7.toNat ≤ 281474976710656 ∧
      (0 < w7.toNat → m0.accessible w8.toNat w7.toNat false = true) ∧
      strBytes w2 w8.toNat w7.toNat = strBytes m1 p n)
    (hb : strBytes m1 p n = bs) : StrOut w2 w8.toNat w7.toNat bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, by simpa using h2, fun hp => (hacc _ _).trans (h3 hp), h4.trans hb⟩
  rw [h1, ← hl]; simp [strBytes]

theorem hex_strbytes (m : Memory) (A nib v zW : Nat) (hzW : zW ≤ 3) (hn1 : 1 ≤ nib)
    (hn2 : nib ≤ 16 * (zW + 1)) (hdn : hexDigits v nib)
    (hbuf : ∀ p, 16 * (3 - zW) ≤ p → p < 64 → m.readLE (A + 2 + p) 1 = hexChar (dig v p)) :
    strBytes ((m.writeLE (A + (64 - nib)) 1 48).writeLE (A + (64 - nib + 1)) 1 120) (A + (64 - nib)) (nib + 2)
      = hexStrBytes v nib := by
  apply List.ext_getElem
  · simp [strBytes, hexStrBytes]
  · intro i h1 h2
    simp only [strBytes, hexStrBytes, List.getElem_map, List.getElem_range, List.length_map, List.length_range, List.length_cons] at h1 h2 ⊢
    rcases i with _ | _ | j
    · rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
      simp
    · rw [Janus.Arm64.Memory.bytes_writeLE_inside _ (by omega) (by omega)]
      have e : A + (64 - nib) + (0 + 1) - (A + (64 - nib + 1)) = 0 := by omega
      simp [e]
    · rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega), ← Janus.Arm64.Memory.readLE_one]
      have hj : j < nib := by omega
      have := hbuf (64 - nib + j) (by omega) (by omega)
      rw [show A + (64 - nib) + (j + 1 + 1) = A + 2 + (64 - nib + j) by omega, this]
      simp [dig, List.getElem_map]
      rw [show 63 - (64 - nib + j) = nib - 1 - j by omega]

end Fv256.Hex
