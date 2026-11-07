import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Amd64.Float64J0
import Fv256.Amd64.Float64J1
import Fv256.Amd64.Float64J2
import Fv256.Amd64.Float64J3

/-!
# `(*uint256.Int).Float64() float64` (amd64)

**Guarantee.** For every receiver `x` (`RAX`) whose 32 bytes are readable (below `2^48`) and every Go call in which the stack-growth
check falls through (`StackGuardOK s 0`), the window `[RSP-80, RSP+8)` (the 0x50-byte frame with the saved frame pointer and the
pushed return address of the callee, plus the caller's return-address slot) is writable, `x` does not overlap it, and the SSE control
word has the Go ABI's control bits (`GoMXCSR`): the call returns (no fault, no panic), obeys the ABI, the low 64 bits of `XMM0` are
`Fv256.B.float64BitsNearest` of the number at `x` (IEEE 754 binary64 bits: round-to-nearest-even `convertFromInt` below `2^64`, truncation
of the 52 bits after the leading one from `2^64` on, as the library does), and no byte outside the window changes.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns with the stated result.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Float Janus.Amd64.FP

namespace Fv256.Amd64.Float64

theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s)
      (fun s s' => (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)]) := by
  intro ret hret s hs hpre
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · by_cases h2 : s.mem.readLE (x.toNat + 16) 8 = 0
    · by_cases h1 : s.mem.readLE (x.toNat + 8) 8 = 0
      · exact lem0 x ret hret s hs ⟨hpre, h3, h2, h1⟩
      · exact lem1 x ret hret s hs ⟨hpre, h2, h3, h1⟩
    · exact lem2 x ret hret s hs ⟨hpre, h3, h2⟩
  · exact lem3 x ret hret s hs ⟨hpre, h3⟩

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def x : BitVec 64 := BitVec.ofNat 64 DST

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 wsp else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 80 8 ∧ Buffer s0 x 32 false ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 80 ∨ (s0.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s0 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold regSP; decide,
    by unfold GoMXCSR; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 80 8 ∧ Buffer s x 32 false ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 80 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧ GoMXCSR s) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s x 32) ∧
        MemFrame s.mem s'.mem [((s.regs regSP).toNat - 80, (s.regs regSP).toNat + 8)] :=
  ⟨ret, s0, x, hret, setup, hpre,
    correctness x ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.xmm 0).toNat % 2 ^ 64 = Fv256.B.float64BitsNearest (valueAt s0 x 32) ∧
      MemFrame s0.mem s'.mem [((s0.regs regSP).toNat - 80, (s0.regs regSP).toNat + 8)] :=
  correctness x ret hret s0 setup hpre

end Witness

end Fv256.Amd64.Float64
