import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).ReverseBytes(x *Int) *Int` (arm64)

**Spec (documented).** "ReverseBytes sets z to the value of x with x's 32-byte representation reversed." The 32-byte
representation of an `Int` in memory is its four little-endian limbs, i.e. little-endian bytes `b0..b31`; reversing it gives
`b31..b0`, whose little-endian reading is the big-endian reading `Fv256.Spec.fromBE` of `b0..b31`.

**Guarantee.** For all pointers `z` (receiver, `X0`) and `x` (`X1`), the 32 bytes at `z` writable, those at `x` readable (below `2^48`),
`z` and `x` equal or disjoint: the call returns, obeys the ABI, returns `z`, the number at `z` afterwards is
`Spec.fromBE` of the 32 bytes at `x` (read before the call), and no byte outside `z[0..32)` changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.ReverseBytes

theorem correctness (z x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (x.toNat + i) 1) 32 ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩
  janus_intro hs
  rcases hzx with rfl | hzx
  all_goals simp only [Disjoint] at *
  all_goals first | (exfalso; omega) | (janus_run; rw [Util.be32_rev]; rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _)]; omega)

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
    (Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) :=
  ⟨ret, s0, z, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.ReverseBytes
