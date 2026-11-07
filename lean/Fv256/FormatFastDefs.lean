import Janus

/-!
# `(*uint256.Int).Format`, fast path (ii): shared definitions (amd64 and arm64, Extracted-free)

* `RT`: several-exit reachability (`ReachesRet` with a list of target addresses, each with its own state predicate).
* `FL`: the memory frame the fast path may touch.
-/

open Janus

namespace Fv256.FormatFast

/-- ordinary steps from `S` reach one of the listed addresses with the paired predicate (amd64) -/
def RT (p : Janus.Amd64.Program) (S : Janus.Amd64.State) (T : List (Nat × (Janus.Amd64.State → Prop))) : Prop :=
  ∃ k S', Janus.Amd64.Program.Steps p S k S' ∧ ∃ t ∈ T, S'.rip = BitVec.ofNat 64 t.1 ∧ t.2 S'

theorem RT.of_reachesRet {p : Janus.Amd64.Program} {S : Janus.Amd64.State} {pc : Nat} {Q : Janus.Amd64.State → Prop}
    (h : Janus.Amd64.Tactic.ReachesRet p (BitVec.ofNat 64 pc) S Q) : RT p S [(pc, Q)] := by
  obtain ⟨k, S', hs, hr, hq⟩ := h
  exact ⟨k, S', hs, (pc, Q), List.mem_singleton_self _, hr, hq⟩

theorem RT.trans {p : Janus.Amd64.Program} {S : Janus.Amd64.State} {T T' : List (Nat × (Janus.Amd64.State → Prop))}
    (h : RT p S T)
    (hk : ∀ t ∈ T, ∀ S', S'.rip = BitVec.ofNat 64 t.1 → t.2 S' → RT p S' T') : RT p S T' := by
  obtain ⟨k, S', hs, t, ht, hr, hq⟩ := h
  obtain ⟨j, S'', hs2, r⟩ := hk t ht S' hr hq
  exact ⟨k + j, S'', hs.trans hs2, r⟩

theorem RT.widen {p : Janus.Amd64.Program} {S : Janus.Amd64.State} {T T' : List (Nat × (Janus.Amd64.State → Prop))}
    (h : RT p S T)
    (hT : ∀ t ∈ T, ∃ t' ∈ T', t'.1 = t.1 ∧ ∀ s, t.2 s → t'.2 s) : RT p S T' := by
  obtain ⟨k, S', hs, t, ht, hr, hq⟩ := h
  obtain ⟨t', ht', h1, h2⟩ := hT t ht
  exact ⟨k, S', hs, t', ht', by rw [h1]; exact hr, h2 _ hq⟩

theorem setWidth8_eq_zero (x : BitVec 64) : (BitVec.setWidth 8 x = 0#8) ↔ x.toNat % 256 = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [BitVec.toNat_setWidth] using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_setWidth] using h

/-- the frame list of the fast path: the callee windows `[r - 8 - stack, r + 32)` and the spill slots `[r + 0x50, r + 0x6c)` -/
def FL (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  rt ++ [(r - 8 - stack, r + 32), (r + 0x50, r + 0x6c)]


open Janus.Amd64 Janus.Contracts.ICall in
/-- the standing precondition of the fast path, at the state `S0` just after the `z != 0` split (`Format+0x45`, amd64):
`r = RSP` is the local frame (entry RSP - 72); `[RSP+0x58] = tab`, `[RSP+0x60] = data` are the spilled interface words -/
def FPre (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (S0 : State) : Prop :=
  S0.regs 0 = z ∧ S0.regs 3 = tab ∧ S0.regs 1 = data ∧ S0.regs 5 = S0.regs 4 + 64#64 ∧
  (S0.regs 4).toNat % 8 = 0 ∧ 8 + stack ≤ (S0.regs 4).toNat ∧ (S0.regs 4).toNat + 0x78 ≤ 2 ^ 48 ∧
  S0.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true ∧
  Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt ∧
  S0.mem.readLE ((S0.regs 4).toNat + 0x58) 8 = tab.toNat ∧ S0.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat ∧
  CodePtrOK64 fW ∧ CodePtrOK64 fP ∧ CodePtrOK64 fF ∧ CodePtrOK64 fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ S0.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  S0.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ S0.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  S0.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ S0.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x38 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ tab.toNat + 0x18) ∧
  z.toNat + 32 ≤ 2 ^ 48 ∧ S0.mem.accessible z.toNat 32 false = true ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ z.toNat)

/-- the invariant between the sites: registers `RSP/RBP/R14/X15` kept, memory changed only in `FL`, the spills hold `z, tab, data, ch` -/
def FInv (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (ch32 : Nat) (S0 S : Janus.Amd64.State) : Prop :=
  S.regs 4 = S0.regs 4 ∧ S.regs 5 = S0.regs 5 ∧ S.regs 14 = S0.regs 14 ∧ S.xmm 15 = S0.xmm 15 ∧ S.df = S0.df ∧
  S.fsBase = S0.fsBase ∧ MemFrame S0.mem S.mem (FL rt (S0.regs 4).toNat stack) ∧
  S.mem.readLE ((S0.regs 4).toNat + 0x50) 8 = z.toNat ∧ S.mem.readLE ((S0.regs 4).toNat + 0x58) 8 = tab.toNat ∧
  S.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat ∧ S.mem.readLE ((S0.regs 4).toNat + 0x68) 4 = ch32

end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

theorem sub8_toNat (x : BitVec 64) (h : 8 ≤ x.toNat) : (x - 8#64).toNat = x.toNat - 8 := by
  rw [BitVec.toNat_sub]; simp; omega

theorem add8_toNat (x : BitVec 64) (h : x.toNat + 8 < 2 ^ 64) : (x + 8#64).toNat = x.toNat + 8 := by
  rw [BitVec.toNat_add]; simp; omega
end Fv256.FormatFast

namespace Fv256.FormatFast
theorem mod8 (v : BitVec 64) : v.toNat % 256 ^ 8 = v.toNat := Nat.mod_eq_of_lt (by have := v.isLt; simpa using this)
theorem mod4 (x : Nat) : x % 4294967296 % 256 ^ 4 = x % 4294967296 := by
  have h1 := Nat.mod_lt x (show 0 < 4294967296 by decide)
  have h2 : (256 : Nat) ^ 4 = 4294967296 := by decide
  exact Nat.mod_eq_of_lt (by omega)
theorem sub_add8 (x : BitVec 64) : x - 8#64 + 8#64 = x := BitVec.sub_add_cancel x 8#64
end Fv256.FormatFast

namespace Fv256.FormatFast
/-- a range inside the spill area `[r+0x50, r+0x6c)` is outside the ranges a 1-argument callee may write -/
theorem out_cs1 {rt : List (Nat × Nat)} {r stack a n : Nat} (hout : Outside (r - 8 - stack) (stack + 0x80) rt)
    (h8 : 8 + stack ≤ r) (h1 : r + 0x50 ≤ a) (h2 : a + n ≤ r + 0x6c) :
    Outside a n (rt ++ [(r - 8 - stack, r - 8), (r - 8 + 8, r - 8 + 8 + 8)]) := by
  simp only [outside_append, outside_cons, outside_nil]
  refine ⟨hout.of_sub (by omega) (by omega), ?_, ?_, trivial⟩ <;> omega
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

theorem finv_of {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State}
    (hi : FInv rt stack z tab data ch S0 S) (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5)
    (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15) (hdf : S'.df = S.df) (hfs : S'.fsBase = S.fsBase)
    (hm : S'.mem = S.mem) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a5, a14, ax, adf, afs, afr, r50, r58, r60, r68⟩ := hi
  exact ⟨h4.trans a4, h5.trans a5, h14.trans a14, hx.trans ax, hdf.trans adf, hfs.trans afs, hm ▸ afr, hm ▸ r50, hm ▸ r58,
    hm ▸ r60, hm ▸ r68⟩
end Fv256.FormatFast
