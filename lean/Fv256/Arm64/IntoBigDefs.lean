import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).IntoBig(b **big.Int)` (arm64): the statement pieces

```go
func (z *Int) IntoBig(b **big.Int) {
	if z == nil { *b = nil; return }
	if *b == nil { *b = new(big.Int) }
	if words := (*b).Bits(); cap(words) >= 4 {
		words = words[:4]; words[0..3] = z[0..3]; (*b).SetBits(words)
	} else {
		words := [4]big.Word{z[0], z[1], z[2], z[3]}; (*b).SetBits(words[:])
	}
}
```
`big.Int` is `{neg bool; abs []Word}` (32 bytes: neg at +0, ptr at +8, len at +16, cap at +24).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

def nm : String := "github.com/holiman/uint256.(*Int).IntoBig"

/-- The type descriptor of `big.Int` passed to `newobject` (`ADRP`+`ADD` at `IntoBig+0x2c`). -/
def bigType : Nat :=
  adrpLdTarget (Extracted.entry + 0x2c) (segWord Extracted.program nm 11) (segWord Extracted.program nm 12) 0
/-- The type descriptor of `[4]big.Word` (`ADRP`+`ADD` at `IntoBig+0xa0`). -/
def arrType : Nat :=
  adrpLdTarget (Extracted.entry + 0xa0) (segWord Extracted.program nm 40) (segWord Extracted.program nm 41) 0
/-- The address of the write-barrier flag `runtime.writeBarrier` (`ADRP`+`LDR W` at `IntoBig+0x38`). -/
def flagAddr : Nat :=
  adrpLdTarget (Extracted.entry + 0x38) (segWord Extracted.program nm 14) (segWord Extracted.program nm 15) 2

/-- The content of the `big.Int` that `*bp` points to in `m`: sign flag clear, a normalized magnitude of at most
four words of capacity at least four, equal to `v`. -/
def BigOut (m : Memory) (bp P v : Nat) : Prop :=
  ∃ ap len cap : Nat, m.readLE bp 8 = P ∧ m.accessible P 32 true = true ∧ P + 32 ≤ 2 ^ 48 ∧
    m.readLE P 1 = 0 ∧ m.readLE (P + 8) 8 = ap ∧ m.readLE (P + 16) 8 = len ∧ m.readLE (P + 24) 8 = cap ∧
    4 ≤ cap ∧ m.accessible ap 32 true = true ∧ ap + 32 ≤ 2 ^ 48 ∧ len ≤ 4 ∧
    (len = 0 ∨ m.readLE (ap + 8 * (len - 1)) 8 ≠ 0) ∧
    Fv256.C.bigAbs (fun i => m.readLE (ap + 8 * i) 8) len = v

/-- The content of the `big.Int` object at `P` alone (without the slot that points to it). -/
def BigObj (m : Memory) (P v : Nat) : Prop :=
  ∃ ap len cap : Nat, m.accessible P 32 true = true ∧ P + 32 ≤ 2 ^ 48 ∧
    m.readLE P 1 = 0 ∧ m.readLE (P + 8) 8 = ap ∧ m.readLE (P + 16) 8 = len ∧ m.readLE (P + 24) 8 = cap ∧
    4 ≤ cap ∧ m.accessible ap 32 true = true ∧ ap + 32 ≤ 2 ^ 48 ∧ len ≤ 4 ∧
    (len = 0 ∨ m.readLE (ap + 8 * (len - 1)) 8 ≠ 0) ∧
    Fv256.C.bigAbs (fun i => m.readLE (ap + 8 * i) 8) len = v

theorem BigObj.of_bigOut {m : Memory} {bp P v : Nat} (h : BigOut m bp P v) : BigObj m P v := by
  obtain ⟨ap, len, cap, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨ap, len, cap, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  GuardOK s 4144 ∧ StackOK s 4144 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4144) 4168 R.rt ∧ Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4144) 4168 ∧
    Outside ((s.regs 28).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 28).toNat (view R.rt [] s.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ b ∧
    Ptr s.mem bp 8 true ∧ Outside bp.toNat 8 R.rt ∧ Disjoint bp.toNat 8 (s.sp.toNat - 4144) 4168 ∧
    (z.toNat ≠ 0 →
      Ptr s.mem z 32 false ∧ Outside z.toNat 32 R.rt ∧ Disjoint z.toNat 32 (s.sp.toNat - 4144) 4168 ∧
      Disjoint z.toNat 32 bp.toNat 8 ∧
      (s.mem.readLE bp.toNat 8 ≠ 0 →
        Ptr s.mem (BitVec.ofNat 64 (s.mem.readLE bp.toNat 8)) 32 true ∧
        Outside (s.mem.readLE bp.toNat 8) 32 R.rt ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 (s.sp.toNat - 4144) 4168 ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 bp.toNat 8 ∧
        Disjoint (s.mem.readLE bp.toNat 8) 32 z.toNat 32 ∧
        (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
          Ptr s.mem (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8)) 32 true ∧
          Outside (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 R.rt ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.sp.toNat - 4144) 4168 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 bp.toNat 8 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 z.toNat 32 ∧
          Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.mem.readLE bp.toNat 8) 32)))

/-- Extra separation facts of `correctness`: the stack-guard slot `g + 16` is apart from the caller's writable blocks. -/
def PreX (z bp : BitVec 64) (s : State) : Prop :=
  Apart bp.toNat 8 ((s.regs 28).toNat + 16) 8 ∧
    (z.toNat ≠ 0 → s.mem.readLE bp.toNat 8 ≠ 0 →
      s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 < 2 ^ 63 ∧
      Apart (s.mem.readLE bp.toNat 8) 32 ((s.regs 28).toNat + 16) 8 ∧
      (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
        Apart (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 28).toNat + 16) 8))

/-- The postcondition of `correctness`. -/
def Post (R : RtInv) (z bp : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, BigOut s'.mem bp.toNat P (val256 s.mem z.toNat)) ∧
  MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
    (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)])

theorem ZeroBytes.writeLE_apart {m : Memory} {a n x k v : Nat} (h : ZeroBytes m a n)
    (hd : a + n ≤ x ∨ x + k ≤ a) : ZeroBytes (m.writeLE x k v) a n := by
  intro i hi
  rw [Janus.Arm64.Memory.bytes_writeLE_outside _ (by omega)]
  exact h i hi

theorem ZeroBytes.of_liveFrame {m m' : Memory} {L : List (Nat × Nat)} {a n : Nat}
    (hf : LiveFrame m m' L []) (h : ZeroBytes m a n) (hin : InRanges a n L) : ZeroBytes m' a n := by
  intro i hi
  obtain ⟨r, hr, h1, h2⟩ := hin
  have h3 := hf.readLE_nil (a + i) 1 ⟨r, hr, by omega, by omega⟩
  have h4 := h i hi
  have h5 : m.readLE (a + i) 1 = 0 := by rw [Janus.Arm64.Memory.readLE_one, h4]; rfl
  rw [h5] at h3
  rw [Janus.FFI.bytes_eq_readLE, h3]
  rfl

theorem val256_bigAbs (m : Memory) (z : Nat) :
    val256 m z = Fv256.C.bigAbs (fun i => m.readLE (z + 8 * i) 8) 4 := by
  simp only [Fv256.C.bigAbs, show (8 : Nat) * 2 = 16 from rfl, show (8 : Nat) * 3 = 24 from rfl,
    show 64 * 2 = 128 from rfl, show 64 * 3 = 192 from rfl, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.pow_zero, Nat.mul_one, Nat.reducePow, show (8 : Nat) * 1 = 8 from rfl, show 64 * 1 = 64 from rfl]
  rw [Spec.val256_limbs]
  omega

theorem bigAbs_trunc (w : Nat → Nat) (len n : Nat) (hn : len ≤ n) (h : ∀ i, len ≤ i → i < n → w i = 0) :
    Fv256.C.bigAbs w n = Fv256.C.bigAbs w len := by
  induction n with
  | zero =>
    obtain rfl : len = 0 := by omega
    rfl
  | succ n ih =>
    by_cases hl : len = n + 1
    · subst hl; rfl
    · simp only [Fv256.C.bigAbs]
      rw [h n (by omega) (by omega), Nat.zero_mul, Nat.add_zero]
      exact ih (by omega) (fun i hi hi2 => h i hi (by omega))

/-- The closing step: the big.Int at `P` (pointed to by the slot `bp`) holds the normalized limbs `limb`. -/
theorem bigout_of (M : Memory) (bp P A len cap v : Nat) (limb : Nat → Nat)
    (hbp : M.readLE bp 8 = P) (hacc : M.accessible P 32 true = true) (hP48 : P + 32 ≤ 2 ^ 48)
    (hneg : M.readLE P 1 = 0) (hA : M.readLE (P + 8) 8 = A) (hl : M.readLE (P + 16) 8 = len)
    (hc : M.readLE (P + 24) 8 = cap) (hcap : 4 ≤ cap) (haccA : M.accessible A 32 true = true)
    (hA48 : A + 32 ≤ 2 ^ 48) (hlen : len ≤ 4) (hw : ∀ i, i < 4 → M.readLE (A + 8 * i) 8 = limb i)
    (hnorm : len = 0 ∨ limb (len - 1) ≠ 0) (hz : ∀ i, len ≤ i → i < 4 → limb i = 0)
    (hv : v = Fv256.C.bigAbs limb 4) : BigOut M bp P v := by
  refine ⟨A, len, cap, hbp, hacc, hP48, hneg, hA, hl, hc, hcap, haccA, hA48, hlen, ?_, ?_⟩
  · rcases hnorm with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hw (len - 1) (by omega)]; exact h)
  · rw [hv, bigAbs_trunc limb len 4 hlen hz]
    exact Fv256.C.bigAbs_congr _ _ _ (fun i hi => hw i (by omega))

theorem ptr_of {m : Memory} {x n : Nat} {w : Bool} (hx : x < 2 ^ 64) (h : Ptr m (BitVec.ofNat 64 x) n w) :
    m.accessible x n w = true ∧ x + n ≤ 2 ^ 48 := by
  simpa [Ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] using h

theorem cap_slt (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toInt < 4 ↔ (x < 4 ∨ 2 ^ 63 ≤ x) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  split <;> omega

/-- An opaque wrapper: hides a conjunction of (disjunctive) facts from `omega` during a `janus_run`. -/
def Hidden (p : Prop) : Prop := p

/-- Reading memory the write-barrier slots were stored into: a read outside `rt` and the window sees the
memory before the call. -/
theorem read_wb {M0 w2 : Memory} {rt : List (Nat × Nat)} {wl wh w6 x n v1 v2 : Nat}
    (hf : MemFrame M0 w2 (rt ++ [(wl, wh)])) (hs : InRanges w6 16 rt) (hx : Outside x n rt)
    (hxw : x + n ≤ wl ∨ wh ≤ x) :
    ((w2.writeLE w6 8 v1).writeLE (w6 + 8) 8 v2).readLE x n = M0.readLE x n := by
  obtain ⟨r, hr, h1, h2⟩ := hs
  have hd := MemFrame.outside_mem hx hr
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  refine hf.readLE x n ?_
  simp only [outside_append, outside_cons, outside_nil, and_true]
  exact ⟨hx, hxw⟩

/-- The frame of the exits: the stores to the `big.Int` block and the barrier slots. -/
theorem frame_wb {m S M0 w2 : Memory} {rt : List (Nat × Nat)} {sl sh tl th bl bh al ah wl wh : Nat}
    {P len cap w6 a b A' : Nat}
    (h1 : MemFrame m S (rt ++ [(sl, sh), (tl, th), (bl, bh), (al, ah)]))
    (hM0 : M0 = (S.writeLE (P + 16) 8 len).writeLE (P + 24) 8 cap)
    (h2 : MemFrame M0 w2 (rt ++ [(wl, wh)])) (hwin : sl ≤ wl ∧ wh ≤ sh)
    (hs : InRanges w6 16 rt) :
    MemFrame m ((((w2.writeLE w6 8 a).writeLE (w6 + 8) 8 b).writeLE (P + 8) 8 A').writeLE P 1 0)
      (rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)]) := by
  have hL : ∀ a n, Outside a n (rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)]) →
      Outside a n (rt ++ [(sl, sh), (tl, th), (bl, bh), (al, ah)]) := by
    intro a n hh
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.2⟩
  have hA : MemFrame m S (rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)]) := h1.mono hL
  have hB : MemFrame m M0 (rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)]) := by
    rw [hM0]
    refine (hA.writeLE_inRanges _ ?_).writeLE_inRanges _ ?_
    · exact ⟨(P, P + 32), by simp, by omega, by omega⟩
    · exact ⟨(P, P + 32), by simp, by omega, by omega⟩
  have hC : MemFrame m w2 (rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)]) := by
    refine hB.trans h2 ?_
    intro a n hh
    refine ⟨hh, ?_⟩
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    refine ⟨hh.1, ?_⟩
    rcases hh.2.1 with h | h
    · left; omega
    · right; omega
  obtain ⟨r, hr, hr1, hr2⟩ := hs
  have hr' : r ∈ rt ++ [(sl, sh), (tl, th), (bl, bh), (P, P + 32), (al, ah)] := by simp [hr]
  refine (((hC.writeLE_inRanges _ ⟨r, hr', by omega, by omega⟩).writeLE_inRanges _
    ⟨r, hr', by omega, by omega⟩).writeLE_inRanges _ ⟨(P, P + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
    ⟨(P, P + 32), by simp, by omega, by omega⟩

/-- A read equation `m.readLE a n = v` that `simp` does not see (to keep a copy of a fact `simp at *` rewrites). -/
def ReadEq (m : Memory) (a n v : Nat) : Prop := m.readLE a n = v

/-- Reading back the four words stored at `A`. -/
theorem words4 (M : Memory) (A v0 v1 v2 v3 : Nat) (h0 : v0 < 2 ^ 64) (h1 : v1 < 2 ^ 64) (h2 : v2 < 2 ^ 64)
    (h3 : v3 < 2 ^ 64) (i : Nat) (hi : i < 4) :
    ((((M.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3).readLE (A + 8 * i) 8
      = (if i = 0 then v0 else if i = 1 then v1 else if i = 2 then v2 else v3) := by
  have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · simp only [Nat.mul_zero, Nat.add_zero, if_true]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt h0]
  · simp only [Nat.mul_one]
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt h1]
    simp
  · rw [show A + 8 * 2 = A + 16 by omega, Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Janus.Arm64.Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt h2]
    simp
  · rw [show A + 8 * 3 = A + 24 by omega, Janus.Arm64.Memory.readLE_writeLE_self, e, Nat.mod_eq_of_lt h3]
    simp

theorem read_words4 (M : Memory) (A v0 v1 v2 v3 x n : Nat) (h : x + n ≤ A ∨ A + 32 ≤ x) :
    ((((M.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3).readLE x n = M.readLE x n := by
  rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
    Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]

theorem frame_add {m S : Memory} {rt : List (Nat × Nat)} {sl sh tl th bl bh al ah : Nat}
    (h : MemFrame m S (rt ++ [(sl, sh), (tl, th), (bl, bh)])) : MemFrame m S (rt ++ [(sl, sh), (tl, th), (bl, bh), (al, ah)]) :=
  h.mono fun a n hh => by
    simp only [outside_append, outside_cons, outside_nil, and_true] at hh ⊢
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩

theorem view_words4 (rt L : List (Nat × Nat)) (M : Memory) (A v0 v1 v2 v3 : Nat) (hA : Outside A 32 rt) :
    view rt L ((((M.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3) = view rt L M := by
  rw [view_writeLE_out (Outside.of_sub hA (by omega) (by omega)), view_writeLE_out (Outside.of_sub hA (by omega) (by omega)),
    view_writeLE_out (Outside.of_sub hA (by omega) (by omega)), view_writeLE_out (Outside.of_sub hA (by omega) (by omega))]

theorem frame_words4 {m S : Memory} {rt : List (Nat × Nat)} {sl sh tl th bl bh A : Nat} {v0 v1 v2 v3 : Nat}
    (h : MemFrame m S (rt ++ [(sl, sh), (tl, th), (bl, bh), (A, A + 32)])) :
    MemFrame m ((((S.writeLE A 8 v0).writeLE (A + 8) 8 v1).writeLE (A + 16) 8 v2).writeLE (A + 24) 8 v3)
      (rt ++ [(sl, sh), (tl, th), (bl, bh), (A, A + 32)]) :=
  (((h.writeLE_inRanges _ ⟨(A, A + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
    ⟨(A, A + 32), by simp, by omega, by omega⟩).writeLE_inRanges _ ⟨(A, A + 32), by simp, by omega, by omega⟩).writeLE_inRanges _
    ⟨(A, A + 32), by simp, by omega, by omega⟩

/-- The pc after `*b` was loaded (or allocated) and stored: `ldr x2, [x1]` (`IntoBig+0x64`). -/
abbrev pcLoad : Nat := Extracted.entry + 0x64

/-- What every segment boundary state `S` has in common with the call state `s`: the frame (`SP`, `X29`,
the platform and goroutine registers, the return address, the saved frame pointer and the two spilled
arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (z bp : BitVec 64) (s S : State) : Prop :=
  S.sp = s.sp - 48#64 ∧ S.regs 28 = s.regs 28 ∧ S.regs 29 = s.sp - 56#64 ∧ S.regs 18 = s.regs 18 ∧
    S.mem.readLE (s.sp.toNat - 48) 8 = ret ∧ S.mem.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat ∧
    S.mem.readLE (s.sp.toNat + 8) 8 = z.toNat ∧ S.mem.readLE (s.sp.toNat + 16) 8 = bp.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)])

theorem reaches_mono {p : Program} {s : State} {Q Q' : Outcome → Prop} (h : Reaches p s Q) (hQ : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hQ o h2⟩

/-- From the tail's result (`BigOut` and a frame with the new block) to `Post`. -/
theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P : Nat) (hz0 : z.toNat ≠ 0) :
    ∀ o : Outcome,
      IsReturn (fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) o →
      (∀ a n, Outside a n (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8),
          (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
          (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) →
        Outside a n (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) →
      IsReturn (fun s' => ABIReturn s s' ∧ Post R z bp s s') o := by
  intro o ho hw
  cases o with
  | returned s' => exact ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.mono hw⟩
  | stub n k s' => exact ho.elim

end Fv256.Arm64.IntoBig
