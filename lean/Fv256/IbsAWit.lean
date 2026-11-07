import Janus
import Fv256.IndexByteSpec

/-! Satisfiability of `IbsPreA` (amd64): a concrete state with a 5-byte string, so `ibs_summary_A` is not vacuous. -/

namespace Fv256.IndexByte
open Janus Janus.Amd64

namespace WitA

def mem0 : Janus.Arm64.Memory := ⟨fun _ => 0, [⟨0x10000, 0x30000, true⟩, ⟨0x5df000, 0x1000, false⟩]⟩

/-- return address at `[RSP]`, `ptr` `0x30000`, `len` 5, `c` = `'a'` -/
def mem1 : Janus.Arm64.Memory :=
  ((((mem0.writeLE 0x20000 8 0x401000).writeLE 0x20008 8 0x30000).writeLE 0x20010 8 5).writeLE 0x20018 1 0x61)

def st : Janus.Amd64.State :=
  { regs := fun i => if i = 4 then 0x20000 else 0, rip := 0x402bc0, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := mem1 }

theorem nonvacuous : ∃ (p n : BitVec 64) (c : Nat) (s : Janus.Amd64.State),
    s.rip = BitVec.ofNat 64 0x402bc0 ∧ IbsPreA 0x5df444 p n c s := by
  refine ⟨0x30000, 5, 0x61, st, rfl, ?_⟩
  unfold IbsPreA PageReadable st
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end WitA
end Fv256.IndexByte
