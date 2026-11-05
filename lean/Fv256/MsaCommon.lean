import Janus

/-!
# `MarshalSSZAppend`: the ISA-independent budget bound (four 8-byte `append`s)
-/

open Janus Janus.Spec Janus.Contracts

namespace Fv256.Msa

/-- The cost bound of one `growslice` call made with `newLen ≤ len0 + 32`. -/
def Kc (len0 : Nat) : Nat := 2 * (2 * (len0 + 32) + 192) + 24

theorem cost_le (len0 len cc : Nat) (h1 : len + 8 ≤ len0 + 32) (h2 : cc < len + 8) :
    roundupsize (nextslicecap (len + 8) cc) true ≤ Kc len0 := by
  have h3 := nextslicecap_le (len + 8) cc h2
  have h4 := roundupsize_le (nextslicecap (len + 8) cc) true
  unfold Kc
  omega

/-- Wrapper that keeps a hypothesis out of the stepping tactics' reach (a visible `MemFrame s.mem S.mem _` makes the store step stuck). -/
def Hidden (p : Prop) : Prop := p

end Fv256.Msa
