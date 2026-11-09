import Fv256.Proofs.Common.FmTac
import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Common.IntoBigCommon
import Fv256.Spec.Arm64.FM.IntoBigDefs

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.IntoBig

export Fv256.IntoBig (BigOut BigObj)

/-- the data objects IntoBig reads: the types of `big.Int` and of `[4]big.Word`.  Format's extraction has 26 read-only data objects; `janus_data` makes a fact per object of the program's data list, so the precondition speaks of the program with only these two. -/
def ibData : List Janus.DataSegment :=
  Extracted.program.data.filter fun d => d.name == ".rodata+0xdc20" || d.name == ".rodata+0x19b40"

/-- the extracted program with only those data objects -/
def Pib : Program := { Extracted.program with data := ibData }

theorem Pib_dataLoaded {m : Memory} (h : Extracted.program.DataLoaded m) : Pib.DataLoaded m :=
  fun d hd => h d (List.mem_filter.1 hd).1

end Fv256.Arm64.IntoBig

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
