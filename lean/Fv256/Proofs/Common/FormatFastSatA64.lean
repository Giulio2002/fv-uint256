import Fv256.Proofs.Common.FormatFastDefsA64

/-!
# Satisfiability of the standing precondition `FPre` (arm64)

A concrete state meets every conjunct of `FPre` (so the precondition of `fast_arm64` is not vacuous by itself):
`SP = 0x100000`, `stack = 4608`, the itab at `0x40000` with the four code pointers `0x1000, 0x1004, 0x1008, 0x100c`,
`*z` at `0x30000`, `rt = []`.
-/

open Janus Janus.Arm64 Janus.Contracts.ICall Janus.Spec

namespace Fv256.FormatFastA64.Sat

def sp0 : Nat := 0x100000
def zp : Nat := 0x30000
def tabp : Nat := 0x40000
def datap : Nat := 0x50000

def byteOf (w k : Nat) : Byte := BitVec.ofNat 8 (w / 256 ^ k % 256)

def bytes (a : Nat) : Byte :=
  if tabp + 0x18 ≤ a ∧ a < tabp + 0x20 then byteOf 0x1008 (a - (tabp + 0x18))
  else if tabp + 0x20 ≤ a ∧ a < tabp + 0x28 then byteOf 0x1004 (a - (tabp + 0x20))
  else if tabp + 0x28 ≤ a ∧ a < tabp + 0x30 then byteOf 0x1000 (a - (tabp + 0x28))
  else if tabp + 0x30 ≤ a ∧ a < tabp + 0x38 then byteOf 0x100c (a - (tabp + 0x30))
  else if sp0 + 96 ≤ a ∧ a < sp0 + 104 then byteOf tabp (a - (sp0 + 96))
  else if sp0 + 104 ≤ a ∧ a < sp0 + 112 then byteOf datap (a - (sp0 + 104))
  else 0

def S0 : State :=
  { regs := fun i => if i = 0 then BitVec.ofNat 64 zp else if i = 1 then BitVec.ofNat 64 tabp
      else if i = 2 then BitVec.ofNat 64 datap else if i = 29 then BitVec.ofNat 64 (sp0 - 8) else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 0,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4608, 4608 + 0x78, true⟩, ⟨tabp + 0x18, 0x20, false⟩, ⟨zp, 0x20, false⟩]⟩ }

set_option maxRecDepth 100000 in
theorem fpre_sat : FPre [] 4608 (BitVec.ofNat 64 zp) (BitVec.ofNat 64 tabp) (BitVec.ofNat 64 datap) 0x1000 0x1004 0x1008 0x100c S0 := by
  unfold FPre CodePtrOK Ptr32 Ptr
  simp only [outside_nil, true_and]
  repeat' apply And.intro
  all_goals decide

end Fv256.FormatFastA64.Sat
