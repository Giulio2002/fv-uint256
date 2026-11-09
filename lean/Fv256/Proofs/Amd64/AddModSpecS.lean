import Janus
import Fv256.Proofs.Common.SpecF

/-!
# `AddMod` summary statement pieces (Extracted-free)

`AddPre p s`: the precondition of a call of `(*Int).AddMod(z, x, y, m)` (receiver `RAX`, operands `RBX`, `RCX`, `RDI`) at entry state `s`
of program `p`; `AddPost s s'`: the postcondition; `AddCase s`: the guard of the fast path (`m[3] ≠ 0 ∧ x[3] ≤ m[3] ∧ y[3] ≤ m[3]`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.AddModSpecS

abbrev AddPre (p : Janus.Amd64.Program) (s : State) : Prop :=
  (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
  0x380 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0x300 ∧ StackWritable s 0x348 0x28 ∧ p.DataLoaded s.mem ∧ s.xmm 15 = 0 ∧
  Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 3) 32 false ∧ Buffer s (s.regs 1) 32 false ∧ Buffer s (s.regs 7) 32 false ∧
  ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x348 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 0).toNat) ∧
  ((s.regs 3).toNat + 32 ≤ (s.regs 4).toNat - 0x348 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 3).toNat) ∧
  ((s.regs 1).toNat + 32 ≤ (s.regs 4).toNat - 0x348 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 1).toNat) ∧
  ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat - 0x348 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 7).toNat) ∧
  (s.regs 0 = s.regs 7 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 0).toNat) ∧
  (s.regs 0 = s.regs 3 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 3).toNat ∨ (s.regs 3).toNat + 32 ≤ (s.regs 0).toNat) ∧
  (s.regs 0 = s.regs 1 ∨ (s.regs 0).toNat + 32 ≤ (s.regs 1).toNat ∨ (s.regs 1).toNat + 32 ≤ (s.regs 0).toNat) ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x348 ∨ (s.regs 4).toNat + 0x28 ≤ (s.regs 14).toNat + 16) ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 0).toNat ∨ (s.regs 0).toNat + 32 ≤ (s.regs 14).toNat + 16)

abbrev AddPost (s s' : State) : Prop :=
  s'.regs 0 = s.regs 0 ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.mxcsr = s.mxcsr ∧
  s'.mem.readLE (s.regs 0).toNat 32 = Fv256.F.addmodSpec (s.mem.readLE (s.regs 3).toNat 32) (s.mem.readLE (s.regs 1).toNat 32) (s.mem.readLE (s.regs 7).toNat 32) ∧
  MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x348, (s.regs 4).toNat + 0x28)]

abbrev AddCase (s : State) : Prop :=
  s.mem.readLE ((s.regs 7).toNat + 24) 8 ≠ 0 ∧ s.mem.readLE ((s.regs 3).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 7).toNat + 24) 8 ∧
  s.mem.readLE ((s.regs 1).toNat + 24) 8 ≤ s.mem.readLE ((s.regs 7).toNat + 24) 8

end Fv256.Amd64.AddModSpecS
