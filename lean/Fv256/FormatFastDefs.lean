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

namespace Fv256.FormatFast
open Janus.Amd64

/-- the invariant survives an icall: the callee returned in memory `m` (a frame of the call-state memory), registers as `retState64` leaves them -/
theorem finv_call {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {rv e : Nat} (hi : FInv rt stack z tab data ch S0 S) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (hout : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt) (he : e ≤ (S0.regs 4).toNat + 32)
    (hfr : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m
      (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat - 8), ((S0.regs 4).toNat - 8 + 8, e)]))
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15)
    (hdf : S'.df = S.df) (hfs : S'.fsBase = S.fsBase) (hm : S'.mem = m) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a5, a14, ax, adf, afs, afr, r50, r58, r60, r68⟩ := hi
  have h1 : MemFrame S.mem (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.of_writeLE S.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32))
      (List.mem_append_right _ (by simp)) (by omega) (by omega)
  have h2 : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, ?_, trivial⟩ <;> omega)
  have hr : ∀ a n, (S0.regs 4).toNat + 0x50 ≤ a → a + n ≤ (S0.regs 4).toNat + 0x6c →
      m.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hfr.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega, trivial⟩)]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨h4.trans a4, h5.trans a5, h14.trans a14, hx.trans ax, hdf.trans adf, hfs.trans afs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r50
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r58
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r60
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r68
end Fv256.FormatFast

namespace Fv256.FormatFast
theorem nx (b : Nat) : (b ^^^ 1 = 0 ↔ b = 1) := by
  constructor
  · intro h
    have : b = (b ^^^ 1) ^^^ 1 := by rw [Nat.xor_assoc]; simp
    rw [h] at this; simpa using this
  · intro h; subst h; rfl

theorem xor1_zero (x : BitVec 64) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ 1#32)) = 0#8) ↔ x.toNat % 256 = 1 := by
  have h3 : (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ 1#32))).toNat = (x.toNat % 256) ^^^ 1 := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_xor]
    have e1 : (1#32).toNat = 1 := rfl
    rw [e1]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 64)), Nat.xor_mod_two_pow,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 8 ≤ 32))]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [h3] at this
    exact (nx _).1 (by simpa using this)
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [h3]
    simpa using (nx _).2 h
end Fv256.FormatFast

namespace Fv256.FormatFast
theorem sub32_eq_zero (n k : Nat) (hn : n < 2 ^ 32) (hk : k < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 n)) - BitVec.ofNat 32 k = 0#32) ↔ n = k := by
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1
    have e1 : n % 2 ^ 32 % 2 ^ 64 = n % 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
    have e2 : n % 2 ^ 32 = n := Nat.mod_eq_of_lt hn
    have e3 : k % 2 ^ 32 = k := Nat.mod_eq_of_lt hk
    rw [e2, e3] at h1
    have e4 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
    simp only [e4, e2, e1] at h1
    omega
  · intro h; subst h; simp
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

/-- the invariant survives a summary call whose frame is the single window `[r - 8 - k, r)` (`k ≤ stack`) -/
theorem finv_call1 {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {rv k : Nat} (hi : FInv rt stack z tab data ch S0 S) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (hout : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt) (hk : k ≤ stack)
    (hfr : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (rt ++ [((S0.regs 4).toNat - 8 - k, (S0.regs 4).toNat - 8 + 8)]))
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15)
    (hdf : S'.df = S.df) (hfs : S'.fsBase = S.fsBase) (hm : S'.mem = m) : FInv rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a5, a14, ax, adf, afs, afr, r50, r58, r60, r68⟩ := hi
  have h1 : MemFrame S.mem (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.of_writeLE S.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32))
      (List.mem_append_right _ (by simp)) (by omega) (by omega)
  have h2 : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, trivial⟩ <;> omega)
  have hr : ∀ a n, (S0.regs 4).toNat + 0x50 ≤ a → a + n ≤ (S0.regs 4).toNat + 0x6c →
      m.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hfr.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, trivial⟩)]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨h4.trans a4, h5.trans a5, h14.trans a14, hx.trans ax, hdf.trans adf, hfs.trans afs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r50
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r58
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r60
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r68
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

/-- the call-site property of the fast path's `Write(p []byte)` call: the receiver data word, the slice `(ptr, len, cap)` whose
first `len` bytes are readable and equal `bs`, and `len ≤ cap` -/
def FastWP (data : BitVec 64) (bs : List Nat) (sc : State) : Prop :=
  sc.regs 0 = data ∧ Janus.Contracts.StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat bs ∧
    (sc.regs 1).toNat ≤ (sc.regs 7).toNat

end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64
theorem out_fl2 {rt : List (Nat × Nat)} {r stack a n : Nat} (ho : Outside a n rt)
    (h1 : a + n ≤ r - 8 - stack ∨ r + 32 ≤ a) (h2 : a + n ≤ r + 0x50 ∨ r + 0x6c ≤ a) : Outside a n (FL rt r stack) := by
  simp only [FL, outside_append, outside_cons, outside_nil]
  refine ⟨ho, ?_, ?_, trivial⟩ <;> omega
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64
theorem frame_call {rt : List (Nat × Nat)} {stack : Nat} {S0 S : State} {m : Memory} {rv e : Nat}
    (afr : MemFrame S0.mem S.mem (FL rt (S0.regs 4).toNat stack)) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (he : e ≤ (S0.regs 4).toNat + 32)
    (hfr : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m
      (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat - 8), ((S0.regs 4).toNat - 8 + 8, e)])) :
    MemFrame S0.mem m (FL rt (S0.regs 4).toNat stack) := by
  have h1 : MemFrame S.mem (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.of_writeLE S.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32))
      (List.mem_append_right _ (by simp)) (by omega) (by omega)
  have h2 : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, ?_, trivial⟩ <;> omega)
  exact afr.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

/-- the read-only data stays loaded across a memory frame that leaves the data ranges alone and keeps the regions -/
theorem dataLoaded_frame {p : Janus.Amd64.Program} {m m' : Janus.Arm64.Memory} {rs : List (Nat × Nat)} (h : p.DataLoaded m)
    (hr : m'.regions = m.regions) (hfr : MemFrame m m' rs) (ho : ∀ d ∈ p.data, Outside d.base d.bytes.length rs) :
    p.DataLoaded m' := by
  intro d hd
  obtain ⟨h1, h2⟩ := h d hd
  refine ⟨by rw [hr]; exact h1, fun i hi => ?_⟩
  have e := hfr.readLE (d.base + i) 1 ((ho d hd).of_sub (by omega) (by omega))
  rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at e
  rw [e]; exact h2 i hi
end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

theorem RT.here {p : Janus.Amd64.Program} {S : Janus.Amd64.State} {T : List (Nat × (Janus.Amd64.State → Prop))}
    (t : Nat × (Janus.Amd64.State → Prop)) (ht : t ∈ T) (hr : S.rip = BitVec.ofNat 64 t.1) (hq : t.2 S) : RT p S T :=
  ⟨0, S, .refl S, t, ht, hr, hq⟩

open Janus.Contracts.ICall in
/-- the `Width` call answered with result byte `j3` (low byte of `RBX`) -/
def WRes (RW : Res) (data tab rW j3 : BitVec 64) : Prop := ∃ j0 j1, RW data tab data rW j0 j3 j1

open Janus.Contracts.ICall in
/-- the `Precision` call (receiver `data`, `RBX` = `b3` left over from `Width`) answered with `p j3` -/
def PRes (RP : Res) (data b3 : BitVec 64) (fP : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r7 j0 j3 j1, RP data b3 (BitVec.ofNat 64 fP) r7 j0 j3 j1 ∧ p j3

open Janus.Contracts.ICall in
/-- the `Flag(c)` call answered with a result `RAX = j0` satisfying `p j0` -/
def FRes (RF : Res) (data : BitVec 64) (fF c : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r7 j0 j3 j1, RF data (BitVec.ofNat 64 c) (BitVec.ofNat 64 fF) r7 j0 j3 j1 ∧ p j0

/-- the machine reads `Flag('+')`, `Flag(' ')`, `Flag('0')` as true iff the result byte is nonzero -/
def fz (j0 : BitVec 64) : Prop := j0.toNat % 256 = 0
/-- the machine reads `Flag('-')`, `Flag('#')` as true iff the result byte is exactly 1 -/
def fx (j0 : BitVec 64) : Prop := j0.toNat % 256 ≠ 1

open Janus.Contracts.ICall in
/-- every query answered "plain": no width, no precision, none of the five flags (as the machine decides) -/
def PlainHist (RW RP RF : Res) (data tab rW j3 : BitVec 64) (fP fF : Nat) : Prop :=
  ((((((WRes RW data tab rW j3 ∧ j3.toNat % 256 = 0) ∧ PRes RP data j3 fP (fun j => j.toNat % 256 = 0)) ∧
    FRes RF data fF 0x2b fz) ∧ FRes RF data fF 0x20 fz) ∧ FRes RF data fF 0x2d fx) ∧ FRes RF data fF 0x30 fz) ∧
    FRes RF data fF 0x23 fx

end Fv256.FormatFast

namespace Fv256.FormatFast
open Janus.Amd64

/-- `FInv` without the direction flag and `FS` base (a `Summary` callee does not expose them) -/
def FInvD (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (ch32 : Nat) (S0 S : Janus.Amd64.State) : Prop :=
  S.regs 4 = S0.regs 4 ∧ S.regs 5 = S0.regs 5 ∧ S.regs 14 = S0.regs 14 ∧ S.xmm 15 = S0.xmm 15 ∧
  MemFrame S0.mem S.mem (FL rt (S0.regs 4).toNat stack) ∧
  S.mem.readLE ((S0.regs 4).toNat + 0x50) 8 = z.toNat ∧ S.mem.readLE ((S0.regs 4).toNat + 0x58) 8 = tab.toNat ∧
  S.mem.readLE ((S0.regs 4).toNat + 0x60) 8 = data.toNat ∧ S.mem.readLE ((S0.regs 4).toNat + 0x68) 4 = ch32

theorem FInv.toD {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S : State}
    (h : FInv rt stack z tab data ch S0 S) : FInvD rt stack z tab data ch S0 S :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2⟩

theorem finvD_call {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {rv e : Nat} (hi : FInvD rt stack z tab data ch S0 S) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (hout : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt) (he : e ≤ (S0.regs 4).toNat + 32)
    (hfr : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m
      (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat - 8), ((S0.regs 4).toNat - 8 + 8, e)]))
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15)
    (hm : S'.mem = m) : FInvD rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a5, a14, ax, afr, r50, r58, r60, r68⟩ := hi
  have h1 : MemFrame S.mem (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.of_writeLE S.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32))
      (List.mem_append_right _ (by simp)) (by omega) (by omega)
  have h2 : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, ?_, trivial⟩ <;> omega)
  have hr : ∀ a n, (S0.regs 4).toNat + 0x50 ≤ a → a + n ≤ (S0.regs 4).toNat + 0x6c →
      m.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hfr.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, by omega, trivial⟩)]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨h4.trans a4, h5.trans a5, h14.trans a14, hx.trans ax, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r50
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r58
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r60
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r68
theorem finvD_call1 {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {ch : Nat} {S0 S S' : State} {m : Memory}
    {rv k : Nat} (hi : FInvD rt stack z tab data ch S0 S) (hwb : 8 + stack ≤ (S0.regs 4).toNat)
    (hout : Outside ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) rt) (hk : k ≤ stack)
    (hfr : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (rt ++ [((S0.regs 4).toNat - 8 - k, (S0.regs 4).toNat - 8 + 8)]))
    (h4 : S'.regs 4 = S.regs 4) (h5 : S'.regs 5 = S.regs 5) (h14 : S'.regs 14 = S.regs 14) (hx : S'.xmm 15 = S.xmm 15)
    (hm : S'.mem = m) : FInvD rt stack z tab data ch S0 S' := by
  obtain ⟨a4, a5, a14, ax, afr, r50, r58, r60, r68⟩ := hi
  have h1 : MemFrame S.mem (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.of_writeLE S.mem _ (r := ((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat + 32))
      (List.mem_append_right _ (by simp)) (by omega) (by omega)
  have h2 : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 rv) m (FL rt (S0.regs 4).toNat stack) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [FL, outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, trivial⟩ <;> omega)
  have hr : ∀ a n, (S0.regs 4).toNat + 0x50 ≤ a → a + n ≤ (S0.regs 4).toNat + 0x6c →
      m.readLE a n = S.mem.readLE a n := by
    intro a n h1 h2
    rw [hfr.readLE a n (by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨hout.of_sub (by omega) (by omega), by omega, trivial⟩)]
    exact Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)
  refine ⟨h4.trans a4, h5.trans a5, h14.trans a14, hx.trans ax, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm]; exact afr.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r50
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r58
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r60
  · rw [hm, hr _ _ (by omega) (by omega)]; exact r68
end Fv256.FormatFast
