import Fv256.Proofs.Arm64.UnmarshalHex
import Fv256.Spec.Arm64.UnmarshalPost

/-!
# Postconditions of `UnmarshalText` / `UnmarshalJSON` (arm64), Extracted-free

`UnmarshalText(input)`: if `input` starts with `0x`/`0X` the result is `fromHex(string(input))`, otherwise
`SetFromDecimal(string(input))`; the error interface value is returned in `X0`/`X1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalPost

theorem not_hex_short {m : Janus.Arm64.Memory} {p n : Nat} (h : (n : Int) < 2) : ¬ IsHex m p n := by
  intro hh; have := hh.1; omega

theorem decPart_of {C : SfdCfg} {z : BitVec 64} {m : Janus.Arm64.Memory} {p n : Nat} {s' s'' : State}
    (h0 : s''.regs 0 = s'.regs 0) (h1 : s''.regs 1 = s'.regs 1) (hm : s''.mem = s'.mem)
    (hd : DecPart C z m p n s') : DecPart C z m p n s'' := by
  unfold DecPart at *
  rw [h0, h1, hm]; exact hd

theorem hexPart_of {z : BitVec 64} {m : Janus.Arm64.Memory} {p n : Nat} {s' s'' : State}
    (h0 : s''.regs 0 = s'.regs 0) (h1 : s''.regs 1 = s'.regs 1) (hm : s''.mem = s'.mem)
    (hd : HexPart z m p n s') : HexPart z m p n s'' := by
  unfold HexPart at *
  rw [h0, h1, hm]; exact hd

/-- the byte compare of the code: `ldrb w3, [x1, k]; cmp w3, #c` -/
abbrev Bw (m : Janus.Arm64.Memory) (p : Nat) : Nat := (BitVec.setWidth 32 (BitVec.ofNat 64 (m.readLE p 1))).toNat

theorem bw_eq (m : Janus.Arm64.Memory) (p : Nat) : Bw m p = m.readLE p 1 := by
  have hl := Janus.Arm64.Memory.readLE_lt m p 1
  simp only [Nat.reducePow, Nat.pow_one] at hl
  unfold Bw
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem not_hex_b0 {m : Janus.Arm64.Memory} {p n : Nat} (h : ¬ Bw m p = 48) : ¬ IsHex m p n := by
  rw [bw_eq] at h
  exact fun hh => h hh.2.1

theorem not_hex_b1 {m : Janus.Arm64.Memory} {p n : Nat} (hx : ¬ Bw m (p + 1) = 120) (hy : ¬ Bw m (p + 1) = 88) :
    ¬ IsHex m p n := by
  rw [bw_eq] at hx hy
  intro hh
  rcases hh.2.2 with h | h
  · exact hx h
  · exact hy h

theorem hex_of_120 {m : Janus.Arm64.Memory} {p n : Nat} (h1 : ¬ (n : Int) < 2) (h2 : Bw m p = 48)
    (h3 : Bw m (p + 1) = 120) : IsHex m p n := by
  rw [bw_eq] at h2 h3
  exact ⟨by omega, h2, Or.inl h3⟩

theorem hex_of_88 {m : Janus.Arm64.Memory} {p n : Nat} (h1 : ¬ (n : Int) < 2) (h2 : Bw m p = 48)
    (h3 : Bw m (p + 1) = 88) : IsHex m p n := by
  rw [bw_eq] at h2 h3
  exact ⟨by omega, h2, Or.inr h3⟩

end Fv256.Arm64.UnmarshalPost
