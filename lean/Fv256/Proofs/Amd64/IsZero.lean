import Extracted
import Fv256.Proofs.Common.Spec

/-!
# `(*uint256.Int).IsZero() bool` (amd64)

**Guarantee.** For every pointer `x` and every Go call state of the compiled method with `x` in
`RAX`, whose return-address slot is writable and such that the 32 bytes at `x` are readable
(below `2^48`), the call returns (never faulting or panicking), obeys the ABI, and the `bool`
result (`AL`, the low byte of `RAX`) is `1` iff the 256-bit little-endian value at `x` is `0`
(`Fv256.Spec.isZero`).

**Non-vacuity.** `Wit.nonvacuous`: the precondition holds for a concrete call state;
`Wit.returns`: that call returns `true` (the zero array).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec

namespace Fv256.Amd64.IsZero

theorem readLE_32 (m : Memory) (a : Nat) :
    m.readLE a 32 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 +
      2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 := by
  rw [show 32 = 8 + 24 from rfl, Janus.Arm64.Memory.readLE_add, show 24 = 8 + 16 from rfl,
    Janus.Arm64.Memory.readLE_add, show 16 = 8 + 8 from rfl, Janus.Arm64.Memory.readLE_add]
  simp only [Nat.add_assoc]
  omega

theorem correctness_proof (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧ Buffer s x 32 false)
      (fun s s' => (s'.regs 0).toNat % 256 = (Spec.isZero (valueAt s x 32)).toNat) := by
  intro ret hret s hs ⟨hsw, hx, hx'⟩
  janus64_intro hs
  obtain ⟨-, hnw, hacc⟩ := hsw
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  have b := fun a => Janus.Arm64.Memory.readLE_lt s.mem a 8
  have b0 := b x.toNat; have b1 := b (x.toNat + 8); have b2 := b (x.toNat + 16)
  have b3 := b (x.toNat + 24)
  simp only [Nat.reducePow] at b0 b1 b2 b3
  janus64_run [readLE_32]
  simp only [Spec.isZero, BitVec.toNat_or, BitVec.toNat_ofNat, Nat.reducePow]
  generalize s.mem.readLE x.toNat 8 = a at b0 ⊢
  generalize s.mem.readLE (x.toNat + 8) 8 = b at b1 ⊢
  generalize s.mem.readLE (x.toNat + 16) 8 = c at b2 ⊢
  generalize s.mem.readLE (x.toNat + 24) 8 = d at b3 ⊢
  rw [Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3]
  simp only [Nat.or_eq_zero_iff]
  by_cases h : ((a = 0 ∧ b = 0) ∧ c = 0) ∧ d = 0
  · have h2 : a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
        6277101735386680763835789423207666416102355444464034512896 * d = 0 := by omega
    rw [if_pos h, (beq_iff_eq).2 h2]; decide
  · have h2 : ¬ (a + 18446744073709551616 * b + 340282366920938463463374607431768211456 * c +
        6277101735386680763835789423207666416102355444464034512896 * d = 0) := by omega
    rw [if_neg h, beq_eq_false_iff_ne.2 h2]; decide

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 x 32 false :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (StackWritable s 0 8 ∧ Buffer s x 32 false) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat % 256 = (Spec.isZero (valueAt s x 32)).toNat :=
  ⟨ret, s0, x, hret, setup, hpre,
    correctness_proof x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 1 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  decide

end Wit

end Fv256.Amd64.IsZero
