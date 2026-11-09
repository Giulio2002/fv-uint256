import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).BitLen()` (amd64, default GOAMD64=v1 build)

**Guarantee.** For every pointer `x` (the receiver, `RAX`) and every Go call state whose return-address slot is writable and
such that the 32 bytes at `x` are readable (below `2^48`), the call returns (no fault, no panic), obeys the ABI, and the result (`X0`/`RAX`) is the number of significant bits (`Fv256.Spec.bitLen`).

**Note.** The default build uses `BSR` on a limb that may be zero (destination undefined by the ISA); the statement holds for every value of that undefined result (it is replaced by `CMOVE`). Verified against Janus 494e1168 (undefined-value stream), not the pinned revision.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: the result for the zero number.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.BitLen

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackWritable s 0 8 ∧ Buffer s x 32 false)
      (fun s s' => (s'.regs 0).toNat = Spec.bitLen (valueAt s x 32)) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, hx, hx'⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  all_goals (have b0 := Util.readLE8_lt s.mem (x.toNat ); have b1 := Util.readLE8_lt s.mem (x.toNat + 8); have b2 := Util.readLE8_lt s.mem (x.toNat + 16); have b3 := Util.readLE8_lt s.mem (x.toNat + 24); have c0 := Util.clz_bl 64 (s.mem.readLE (x.toNat ) 8) (Util.readLE8_lt s.mem (x.toNat )); have c1 := Util.clz_bl 64 (s.mem.readLE (x.toNat + 8) 8) (Util.readLE8_lt s.mem (x.toNat + 8)); have c2 := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem (x.toNat + 16)); have c3 := Util.clz_bl 64 (s.mem.readLE (x.toNat + 24) 8) (Util.readLE8_lt s.mem (x.toNat + 24)); have nz0 : s.mem.readLE x.toNat 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE x.toNat 8) := fun h => (by simp [Spec.bitLen, h]); have nz1 : s.mem.readLE (x.toNat + 8) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (x.toNat + 8) 8) := fun h => (by simp [Spec.bitLen, h]); have nz2 : s.mem.readLE (x.toNat + 16) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) := fun h => (by simp [Spec.bitLen, h]); have nz3 : s.mem.readLE (x.toNat + 24) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (x.toNat + 24) 8) := fun h => (by simp [Spec.bitLen, h]); have z0 : s.mem.readLE x.toNat 8 = 0 → Spec.bitLen (s.mem.readLE x.toNat 8) = 0 := fun h => (by simp [Spec.bitLen, h]); simp only [Util.readLE8_mod, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *; (try rw [Util.bl_4 _ _ _ _ b0 b1 b2]); (try rw [Util.bl_3 _ _ _ b0 b1 b2]); (try rw [Util.bl_2 _ _ b0 b1]); (try simp only [ne_eq]); (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *) <;> omega)


namespace Witness

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
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = Spec.bitLen (valueAt s x 32) :=
  ⟨ret, s0, x, hret, setup, hpre,
    correctness x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [valueAt]
  decide

end Witness

end Fv256.Amd64.BitLen
