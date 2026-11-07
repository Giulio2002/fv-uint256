import Fv256.Arm64.UnmarshalHex

/-!
# Postconditions of `UnmarshalText` / `UnmarshalJSON` (arm64), Extracted-free

`UnmarshalText(input)`: if `input` starts with `0x`/`0X` the result is `fromHex(string(input))`, otherwise
`SetFromDecimal(string(input))`; the error interface value is returned in `X0`/`X1`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromHexLib

namespace Fv256.Arm64.UnmarshalPost

/-- `input` starts with `0x` or `0X` -/
abbrev IsHex (m : Janus.Arm64.Memory) (p n : Nat) : Prop :=
  2 ≤ n ∧ m.readLE p 1 = 48 ∧ (m.readLE (p + 1) 1 = 120 ∨ m.readLE (p + 1) 1 = 88)

/-- the documented results of the hex path, for the string `(p, n)` read in memory `m` -/
def HexPart (z : BitVec 64) (m : Janus.Arm64.Memory) (p n : Nat) (s' : State) : Prop :=
  (∀ v, parseHex (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
  (∀ e, parseHex (bytesAt m p) n = .error e →
      s'.regs 0 = BitVec.ofNat 64 (m.readLE (errAddrOf e) 8) ∧
      s'.regs 1 = BitVec.ofNat 64 (m.readLE (errAddrOf e + 8) 8))

/-- the documented results of the decimal path -/
def DecPart (C : SfdCfg) (z : BitVec 64) (m : Janus.Arm64.Memory) (p n : Nat) (s' : State) : Prop :=
  (∀ v, decParse (bytesAt m p) n = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
  (decParse (bytesAt m p) n = .eof →
      (s'.regs 0).toNat = m.readLE C.ioEOF 8 ∧ (s'.regs 1).toNat = m.readLE (C.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0) ∧
  (decParse (bytesAt m p) n = .range →
      (s'.regs 0).toNat = m.readLE C.errBig 8 ∧ (s'.regs 1).toNat = m.readLE (C.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 m z.toNat) ∧
  (∀ lo' len', decParse (bytesAt m p) n = .syntax lo' len' →
      s'.regs 0 = BitVec.ofNat 64 C.numErrItab)

/-- `UnmarshalText` on the string `(p, n)`: hex or decimal result, and the memory frame -/
def UTPost (C : SfdCfg) (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (z : BitVec 64) (p n : Nat) (s s' : State) : Prop :=
  (IsHex s.mem p n → HexPart z s.mem p n s') ∧
  (¬ IsHex s.mem p n → DecPart C z s.mem p n s') ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

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
