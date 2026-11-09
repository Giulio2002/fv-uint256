import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Common.IntoBigCommon
import Fv256.Spec.Amd64.FM.IntoBigDefs

/-! SPECIFICATION part: the definitions the final theorem statements depend on. The proofs are in the module of the same name under `Fv256.Proofs`. -/


open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

/-- the data objects IntoBig reads: the types of `big.Int` and of the 32-byte array -/
def ibData : List Janus.DataSegment :=
  Extracted.program.data.filter fun d => d.name == ".rodata+0xdc80" || d.name == ".rodata+0x19ba0"

/-- the extracted program with only those data objects -/
def Pib : Amd64.Program := { Extracted.program with data := ibData }

theorem Pib_dataLoaded {m : Amd64.Memory} (h : Extracted.program.DataLoaded m) : Pib.DataLoaded m :=
  fun d hd => h d (List.mem_filter.1 hd).1

export Fv256.IntoBig (BigOut BigObj)

end Fv256.Amd64.IntoBig

/-!
# `(*uint256.Int).IntoBig(b **big.Int)` (amd64): the statement pieces

See `Fv256/Arm64/IntoBigDefs.lean` for the Go source and the layout of `big.Int`. The arguments are `AX = z`, `BX = b`;
the return address is at `[RSP]`, the callee pushes `BP` and reserves 16 bytes, spills the arguments to
`[RSP+8]` and `[RSP+16]` (the caller's argument spill area) and calls the runtime from a frame whose window is
`[RSP - 4128, RSP)`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

export Fv256.IntoBig (BigOut BigObj BigObj.of_bigOut ZeroBytes.writeLE_apart ZeroBytes.of_liveFrame val256_bigAbs bigAbs_trunc bigout_of Hidden read_wb frame_wb ReadEq words4 read_words4 frame_add view_words4 frame_words4)

theorem ptr_of {s : State} {x n : Nat} {w : Bool} (hx : x < 2 ^ 64) (h : Buffer s (BitVec.ofNat 64 x) n w) :
    s.mem.accessible x n w = true ∧ x + n ≤ 2 ^ 48 := by
  obtain ⟨h1, h2⟩ := h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at h1 h2
  exact ⟨h2, h1⟩

/-- The pc after `*b` was loaded (or allocated) and stored: `mov (%rbx),%rcx` (`IntoBig+0x68`). -/
abbrev pcLoad : Nat := ibE + 0x68

/-- What every segment boundary state `S` has in common with the call state `s`: the frame (`RSP`, `RBP`,
the goroutine register, the saved frame pointer and the two spilled arguments) and the memory frame. -/
def Rel (R : RtInv) (ret : Nat) (z bp : BitVec 64) (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 24#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.regs 14 = s.regs 14 ∧
    S.mem.readLE (s.regs 4).toNat 8 = ret ∧
    S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = bp.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)])

theorem reaches_mono {p : Amd64.Program} {s : State} {Q Q' : Amd64.Outcome → Prop} (h : Reaches p s Q) (hQ : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hQ o h2⟩

/-- From the tail's result (`BigOut` and a frame with the new block) to `Post`. -/
theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P A : Nat) (hz0 : z.toNat ≠ 0)
    (hPin : s.mem.readLE bp.toNat 8 = 0 → InRanges P 32 R.rt)
    (hn : s.mem.readLE bp.toNat 8 = 0 → ∀ a n,
      Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
        (bp.toNat, bp.toNat + 8)]) →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) :
    ∀ o : Amd64.Outcome,
      IsReturn (fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)]) ∧ (s'.mem.readLE (P + 8) 8 = A ∧ InRanges A 32 R.rt)) o →
      (∀ a n, Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8),
          (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
          (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) →
      IsReturn (fun s' => ABIReturn s s' ∧ Post R z bp s s') o := by
  intro o ho hw
  cases o with
  | returned s' =>
    refine ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.1.mono hw, fun h0 => ho.2.2.1.mono (hn h0), fun _ h0 => ?_⟩
    obtain ⟨ap, len, cap, hbp, -⟩ := ho.2.1
    rw [hbp, ho.2.2.2.1]
    exact ⟨hPin h0, ho.2.2.2.2⟩
  | stub n k s' => exact ho.elim

end Fv256.Amd64.IntoBig
