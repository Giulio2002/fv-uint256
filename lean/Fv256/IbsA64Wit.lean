import Janus
import Fv256.IndexByteSpec

/-! Satisfiability of `IbsPre64` (arm64): a concrete state with a 5-byte string at `0x30001` (unaligned), so `ibs_summary_64` is not vacuous. -/

namespace Fv256.IndexByte
open Janus Janus.Arm64

namespace WitA64

def mem0 : Janus.Arm64.Memory := ⟨fun _ => 0, [⟨0x10000, 0x30000, false⟩]⟩

def st : Janus.Arm64.State :=
  { regs := fun i => if i = 0 then 0x30001 else if i = 1 then 5 else if i = 2 then 0x61 else if i = 30 then 0x1000 else 0
    sp := 0x20000, pc := 0x11f10, flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem nonvacuous : ∃ (p n : BitVec 64) (c : Nat) (s : Janus.Arm64.State),
    s.pc = BitVec.ofNat 64 0x11f10 ∧ IbsPre64 p n c s := by
  refine ⟨0x30001, 5, 0x61, st, rfl, ?_⟩
  unfold IbsPre64 PageReadable st
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end WitA64
end Fv256.IndexByte
