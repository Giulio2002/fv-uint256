import Janus
import Fv256.MsaCommon

/-!
# `MarshalSSZAppend` (amd64): the block invariant (Extracted-free)

The function is four sequential 8-byte appends; each has its own capacity check and its own `runtime.growslice` call.
`BI` holds at the first instruction of block `k` (the load of limb `k`, `RDX = len + 8` already), `k = 0..3`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts
open Janus.Arm64 (Memory)

namespace Fv256.Amd64.Msa

open Fv256.Msa

/-- The requests the runtime must accept: `m` blocks remain, the next one needs length `n` and the slice has capacity `c`
(a `growslice(p, n, c, 8, uint8)` call is made exactly when `c < n`; its result capacity is `growCap 1 true n c`).
The only request parameter that is not determined by the arguments is the old pointer `p`. -/
def Ready (R : RtInv) (ga u8 : Nat) : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | m + 1, n, c => (c < n → (∀ p, R.ok ga [p, n, c, 8, u8]) ∧ Ready R ga u8 m (n + 8) (growCap 1 true n c)) ∧
      (n ≤ c → Ready R ga u8 m (n + 8) c)

/-- The invariant at the start of block `k`: the slice `(pp, len, cc)` (so `len + 8` is what the next append needs; `len = len0 + 8k`),
the frame of the function, the memory facts, the runtime's invariant for the live set `L` and the budget `b`. -/
structure BI (R : RtInv) (ga u8 : Nat) (s S : State) (z : BitVec 64) (ret dp len0 cap0 : Nat) (len pp cc : BitVec 64) (b : Nat)
    (L : List (Nat × Nat)) (m : Nat) : Prop where
  sp : S.regs 4 = s.regs 4 - 104#64
  r0 : S.regs 0 = z
  r3 : S.regs 3 = pp
  r2 : S.regs 2 = len + 8#64
  r7 : S.regs 7 = cc
  r5 : S.regs 5 = s.regs 4 - 8#64
  r14 : S.regs 14 = s.regs 14
  x15 : S.xmm 15 = s.xmm 15
  h_rd1 : S.mem.readLE (s.regs 4).toNat 8 = ret
  h_rd2 : S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat
  h_rd3 : S.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat
  hw : S.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 24) true = true
  frame : MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24), (dp + len0, dp + cap0)])
  noGrow : len0 + 32 ≤ cap0 → pp.toNat = dp ∧ cc.toNat = cap0 ∧
    MemFrame s.mem S.mem [(dp + len0, dp + len.toNat), ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]
  zsame : ∀ i, i < 4 → S.mem.readLE (z.toNat + 8 * i) 8 = s.mem.readLE (z.toNat + 8 * i) 8
  inv : R.inv b L (s.regs 14).toNat (view R.rt L S.mem)
  hLs : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 24)]
  hzL : InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt
  zpd : Apart z.toNat 32 pp.toNat cc.toNat
  lge : len0 ≤ len.toNat
  lle : len.toNat + 8 ≤ len0 + 32
  lc : len.toNat ≤ cc.toNat
  Cb : cc.toNat < 2 ^ 44
  Pb : pp.toNat + cc.toNat ≤ 2 ^ 48
  hdj : Apart pp.toNat cc.toNat ((s.regs 4).toNat - 4208) 4232
  room : len.toNat + 8 ≤ cc.toNat → S.mem.accessible pp.toNat cc.toNat true = true ∧
    (InRanges pp.toNat cc.toNat L ∨ Outside pp.toNat cc.toNat R.rt)
  grow : cc.toNat < len.toNat + 8 → (0 < len.toNat → S.mem.accessible pp.toNat len.toNat false = true)
  bud : m * Kc len0 ≤ b
  rdy : Ready R ga u8 m (len.toNat + 8) cc.toNat
  who : (pp.toNat = dp ∧ cc.toNat = cap0) ∨ InRanges pp.toNat cc.toNat R.rt
  pre : ∀ i, i < len0 → S.mem.bytes (pp.toNat + i) = s.mem.bytes (dp + i)
  mid : S.mem.readLE (pp.toNat + len0) (len.toNat - len0) = s.mem.readLE z.toNat (len.toNat - len0)

end Fv256.Amd64.Msa
