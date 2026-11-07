import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).Bytes20() [20]byte` (amd64)

**Guarantee.** For every receiver `z` (`RAX`) and every Go call such that the return-address slot and the frame window
`[RSP-40, RSP+40)` (the saved frame pointer, a local copy of the array, and the 20 result bytes the callee returns in the caller's
frame at `RSP+8`) are writable, the 32 bytes at `z` are readable (below `2^48`) and do not overlap that window: the call returns
(no fault, no panic), obeys the ABI, the 20 result bytes at `RSP+8` read as the big-endian number (`Fv256.Spec.fromBE`) equal to the
low 160 bits of the number at `z` (read before the call), and no byte changes outside the result bytes and the frame window (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.Bytes20

set_option maxHeartbeats 8000000 in
theorem correctness (z : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z]
      (fun s => StackWritable s 40 40 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat))
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) 20 = valueAt s z 32 % 2 ^ 160 ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 20 ((s.regs regSP).toNat - 40) 40) := by
  intro ret hret s hs ⟨⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  simp only [regSP] at hacc hlow hnw hds
  simp only [valueAt]
  janus64_run [Util.readLE_32]
  refine ⟨?_, ?_⟩
  · rw [Util.b20a_res]
    have l0 := Util.readLE8_lt s.mem z.toNat
    have l1 := Util.readLE8_lt s.mem (z.toNat + 8)
    have l2 := Util.readLE8_lt s.mem (z.toNat + 16)
    have l3 := Util.readLE8_lt s.mem (z.toNat + 24)
    have hr4 := Util.revBytes_lt 4 (s.mem.readLE (z.toNat + 16) 8 % 4294967296)
    have hr1 := Util.revBytes_lt 8 (s.mem.readLE (z.toNat + 8) 8)
    have hr0 := Util.revBytes_lt 8 (s.mem.readLE z.toNat 8)
    simp only [Nat.reducePow] at hr4 hr1 hr0
    have rr4 := Util.rev4_rev4 _ (Nat.mod_lt (s.mem.readLE (z.toNat + 16) 8) (by decide : 0 < 4294967296))
    have rr1 := Util.rev8_rev8 _ l1
    have rr0 := Util.rev8_rev8 _ l0
    generalize Janus.Arm64.revBytesNat 4 (s.mem.readLE (z.toNat + 16) 8 % 4294967296) = r4 at *
    generalize Janus.Arm64.revBytesNat 8 (s.mem.readLE (z.toNat + 8) 8) = R1 at *
    generalize Janus.Arm64.revBytesNat 8 (s.mem.readLE z.toNat 8) = R0 at *
    have e1 : (r4 % 4294967296 + 4294967296 * (R1 % 18446744073709551616) +
        79228162514264337593543950336 * (R0 % 4294967296)) % 4294967296 = r4 := by omega
    have e2 : (R1 % 18446744073709551616 + 18446744073709551616 * (R0 % 18446744073709551616)) % 18446744073709551616 = R1 := by omega
    have e3 : (R1 % 18446744073709551616 + 18446744073709551616 * (R0 % 18446744073709551616)) / 18446744073709551616 % 18446744073709551616 = R0 := by omega
    rw [e1, e2, e3]
    omega
  · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackWritable s0 40 40 ∧ Buffer s0 z 32 false ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 40 ≤ z.toNat) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z] s ∧
    (StackWritable s 40 40 ∧ Buffer s z 32 false ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 40 ≤ z.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE ((s.regs regSP).toNat + 8 + i) 1) 20 = valueAt s z 32 % 2 ^ 160 ∧
        Util.OnlyWrites2 s.mem s'.mem ((s.regs regSP).toNat + 8) 20 ((s.regs regSP).toNat - 40) 40 :=
  ⟨ret, s0, z, hret, setup, hpre,
    correctness z ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧
      Fv256.Spec.fromBE (fun i => s'.mem.readLE ((s0.regs regSP).toNat + 8 + i) 1) 20 = valueAt s0 z 32 % 2 ^ 160 ∧
      Fv256.Util.OnlyWrites2 s0.mem s'.mem ((s0.regs regSP).toNat + 8) 20 ((s0.regs regSP).toNat - 40) 40 :=
  correctness z ret hret s0 setup hpre

end Witness

end Fv256.Amd64.Bytes20
