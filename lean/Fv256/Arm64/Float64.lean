import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Arm64.Float64Lsh
import Fv256.Arm64.Float64J0
import Fv256.Arm64.Float64J1
import Fv256.Arm64.Float64J2
import Fv256.Arm64.Float64J3

/-!
# `(*uint256.Int).Float64() float64` (arm64), master 48f3f44: documented spec "the float64 value nearest to x"

**Guarantee.** For every receiver `x` (`X0`) whose 32 bytes are readable, every Go call state whose stack-growth check falls
through (`GuardOK s 0`), with the 88 bytes below `SP` writable and aligned, disjoint from `x`, and `FPCR = 0`: the call returns, obeys
the ABI, `D0` (as 64 bits) is `Fv256.B.float64BitsNearest` of the 256-bit number at `x` (IEEE 754 binary64 round-to-nearest-even
`convertFromInt`, documented behaviour), and only the 88-byte window below `SP` changes.

The proof splits on the highest non-zero limb (`lem0` .. `lem3`, one module each, so each compiles on its own).

**Non-vacuity.** `Witness.nonvacuous`; `Witness.returns`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0)
      (fun s s' => s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s.mem x.toNat) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat - 88, s.sp.toNat)]) := by
  intro ret hret s hs hpre
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE (x.toNat + 16) 8 = 0
    · by_cases h1 : s.mem.readLE (x.toNat + 8) 8 = 0
      · exact lem0 x ret hret s hs ⟨hpre, h1, h2, h3⟩
      · exact lem1 x ret hret s hs ⟨hpre, h2, h3, h1⟩
    · exact lem2 x ret hret s hs ⟨hpre, h3, h2⟩
  · exact lem3 x ret hret s hs ⟨hpre, h3⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, rfl, by intro i h; simp at h; subst h; rfl⟩

theorem hpre : Ptr32 s0.mem x false ∧ GuardOK s0 0 ∧ StackOK s0 88 0 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 88) 88 ∧ s0.fpcr = 0 :=
  ⟨⟨by decide, by decide⟩, by unfold GuardOK; decide, by unfold StackOK; decide, by unfold Disjoint; decide, rfl⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0) :=
  ⟨ret, s0, x, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.getV 0 64 = Fv256.B.float64BitsNearest (val256 s0.mem x.toNat) ∧
      MemFrame s0.mem s'.mem [(s0.sp.toNat - 88, s0.sp.toNat)] :=
  correctness x ret hret s0 setup hpre

end Witness

end Fv256.Arm64.Float64
