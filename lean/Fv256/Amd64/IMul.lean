import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).IMul(x *Int) *Int` (amd64): in place, `z = z * x`

**Guarantee.** For all pointers `z` (receiver, `RAX`) and `x` (`RBX`) and every Go call state such that the stack-growth check
falls through (`StackGuardOK s 0`), the window `[SP-56, SP+8)` (the frame of `IMul`, the callee's return address, `Mul`'s 16-byte
scratch area and the caller's return-address slot) is writable, the 32 bytes at `z` are writable and those at `x` readable
(below `2^48`), and neither `z` nor `x` overlaps the frame window `[SP-56, SP)` (`z` also not the return-address slot): the call
returns (no fault, no panic), obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.mul` of the
numbers at `z` and `x` before the call, and no byte outside `z[0..32)` and the frame window changes (`Fv256.Util.OnlyWrites2`).
No aliasing assumption between `z` and `x`: the compiled code reads both operands before it writes `z`.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.IMul

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 56 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat ≤ x.toNat))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.mul (valueAt s z 32) (valueAt s x 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 56) 56) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hdx⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hds hdx
  simp only [valueAt, Spec.mul, Disjoint] at *
  janus64_run [Util.readLE_32]
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24));  refine ⟨?_, ?_⟩; (· simp only [Spec.mul, Spec.W, Nat.reducePow, BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reduceMod]; janus64_arith); (· simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]))

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 56 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 56 ∨ (s0.regs regSP).toNat + 8 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 56 ∨ (s0.regs regSP).toNat ≤ x.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 56 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 56 ∨ (s.regs regSP).toNat ≤ x.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.mul (valueAt s z 32) (valueAt s x 32) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 56) 56 :=
  ⟨ret, s0, z, x, hret, setup, hpre,
    correctness z x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = Spec.mul (valueAt s0 z 32) (valueAt s0 x 32) ∧
      Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 ((s0.regs regSP).toNat - 56) 56 :=
  correctness z x ret hret s0 setup hpre

end Witness

end Fv256.Amd64.IMul
