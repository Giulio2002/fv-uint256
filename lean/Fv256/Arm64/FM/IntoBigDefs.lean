import Fv256.FmTac
import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.IntoBigCommon

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

export Fv256.IntoBig (BigOut BigObj BigObj.of_bigOut ZeroBytes.writeLE_apart ZeroBytes.of_liveFrame val256_bigAbs bigAbs_trunc bigout_of Hidden read_wb frame_wb ReadEq words4 read_words4 frame_add view_words4 frame_words4)

/-- IntoBig's entry in Format's extraction (a definition, like `Extracted.entry`, so that offsets stay symbolic) -/
def ibEntry : Nat := 0xb5780

def nm : String := "github.com/holiman/uint256.(*Int).IntoBig"

/-- The type descriptor of `big.Int` passed to `newobject` (`ADRP`+`ADD` at `IntoBig+0x2c`). -/
def bigType : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0x2c) (segWord Extracted.program nm 11) (segWord Extracted.program nm 12) 0
/-- The type descriptor of `[4]big.Word` (`ADRP`+`ADD` at `IntoBig+0xa0`). -/
def arrType : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0xa0) (segWord Extracted.program nm 40) (segWord Extracted.program nm 41) 0
/-- The address of the write-barrier flag `runtime.writeBarrier` (`ADRP`+`LDR W` at `IntoBig+0x38`). -/
def flagAddr : Nat :=
  adrpLdTarget (Fv256.Arm64.IntoBig.ibEntry + 0x38) (segWord Extracted.program nm 14) (segWord Extracted.program nm 15) 2

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
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]))

theorem ptr_of {m : Memory} {x n : Nat} {w : Bool} (hx : x < 2 ^ 64) (h : Ptr m (BitVec.ofNat 64 x) n w) :
    m.accessible x n w = true ∧ x + n ≤ 2 ^ 48 := by
  simpa [Ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] using h

theorem cap_slt (x : Nat) (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x).toInt < 4 ↔ (x < 4 ∨ 2 ^ 63 ≤ x) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  split <;> omega

/-- The pc after `*b` was loaded (or allocated) and stored: `ldr x2, [x1]` (`IntoBig+0x64`). -/
abbrev pcLoad : Nat := Fv256.Arm64.IntoBig.ibEntry + 0x64

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
theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P : Nat) (hz0 : z.toNat ≠ 0)
    (hn : s.mem.readLE bp.toNat 8 = 0 → ∀ a n,
      Outside a n (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8)]) →
        Outside a n (R.rt ++ [(s.sp.toNat - 4144, s.sp.toNat - 8), (s.sp.toNat + 8, s.sp.toNat + 24), (bp.toNat, bp.toNat + 8), (P, P + 32)])) :
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
  | returned s' => exact ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.mono hw, fun h0 => ho.2.2.mono (hn h0)⟩
  | stub n k s' => exact ho.elim

end Fv256.Arm64.IntoBig
