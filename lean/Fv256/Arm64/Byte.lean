import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Byte(n *Int) *Int` (arm64): `z = the n-th byte (from the most significant end) of z`

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`) and every Go call state such that the 32 bytes at `z` are
writable, those at `x` readable (below `2^48`) and `z`, `x` are equal or disjoint, the call returns (no fault, no panic),
obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.byte` of the number at `x` (the index) and the number at `z` before the call,
and no byte outside `z[0..32)` changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z` holding `0`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Byte

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.byte (val256 s.mem x.toNat) (val256 s.mem z.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  · simp only [Disjoint] at *
    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      generalize hN : s.mem.readLE z.toNat 8 = N at *
      have e1 : N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8 = N := (by omega)
      have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (N + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
      rw [e2]
      rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have hq : (18446744073709551616 - N / 8 + 3) % 18446744073709551616 = 3 - N / 8 := (by omega)
      have hr : (18446744073709551616 - 8 * (N % 8) + 56) % 18446744073709551616 % 64 = 8 * (7 - N % 8) := (by omega)
      rw [hq, hr]
      rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      simp only [Spec.byte]
      split <;> omega
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      simp only [Spec.byte]
      split <;> omega
  · simp only [Disjoint] at *
    janus_run [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      generalize hN : s.mem.readLE x.toNat 8 = N at *
      have e1 : N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8 = N := (by omega)
      have e2 : Spec.byte (N + 18446744073709551616 * s.mem.readLE (x.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (x.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (x.toNat + 24) 8) (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) = Spec.byte N (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8) := congrArg (fun a => Spec.byte a (s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 + 340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 + 6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8)) e1
      rw [e2]
      rw [Util.byte_val N _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      have hq : (18446744073709551616 - N / 8 + 3) % 18446744073709551616 = 3 - N / 8 := (by omega)
      have hr : (18446744073709551616 - 8 * (N % 8) + 56) % 18446744073709551616 % 64 = 8 * (7 - N % 8) := (by omega)
      rw [hq, hr]
      rcases (by omega : N / 8 = 0 ∨ N / 8 = 1 ∨ N / 8 = 2 ∨ N / 8 = 3) with h | h | h | h
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
      · rw [h]; simp only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]; simp [hN]
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      simp only [Spec.byte]
      split <;> omega
    · have := Util.readLE8_lt s.mem (z.toNat); have := Util.readLE8_lt s.mem (z.toNat + 8); have := Util.readLE8_lt s.mem (z.toNat + 16); have := Util.readLE8_lt s.mem (z.toNat + 24); have := Util.readLE8_lt s.mem (x.toNat); have := Util.readLE8_lt s.mem (x.toNat + 8); have := Util.readLE8_lt s.mem (x.toNat + 16); have := Util.readLE8_lt s.mem (x.toNat + 24); simp only [Nat.or_eq_zero_iff] at *
      simp only [Spec.byte]
      split <;> omega

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x :=
  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide)⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.byte (val256 s.mem x.toNat) (val256 s.mem z.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.Byte
