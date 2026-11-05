import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.IntoBigCommon

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

/-- The type descriptor of `big.Int` passed to `newobject` (the RIP-relative `LEAQ` at `IntoBig+0x2b`). -/
def bigType : Nat := ripTarget Extracted.program (Extracted.entry + 0x2b)
/-- The type descriptor of `[4]big.Word` (the `LEAQ` at `IntoBig+0xa5`). -/
def arrType : Nat := ripTarget Extracted.program (Extracted.entry + 0xa5)
/-- The address of the write-barrier flag `runtime.writeBarrier` (the `CMPL` at `IntoBig+0x37`). -/
def flagAddr : Nat := ripTarget Extracted.program (Extracted.entry + 0x37)

/-- The precondition of `correctness`. -/
def Pre (R : RtInv) (b : Nat) (z bp : BitVec 64) (s : State) : Prop :=
  StackGuardOK s 4128 ∧ StackWritable s 4128 24 ∧ (s.regs 4).toNat % 8 = 0 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4128) 4152 R.rt ∧ Apart ((s.regs 14).toNat + 16) 8 ((s.regs 4).toNat - 4128) 4152 ∧
    Outside ((s.regs 14).toNat + 16) 8 R.rt ∧
    s.mem.accessible flagAddr 4 false = true ∧ Outside bigType 16 R.rt ∧ Outside arrType 16 R.rt ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType] ∧
    R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
    R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
    R.inv b [] (s.regs 14).toNat (view R.rt [] s.mem) ∧
    blockSize 32 false + blockSize 32 true ≤ b ∧
    Buffer s bp 8 true ∧ Outside bp.toNat 8 R.rt ∧ Janus.Spec.Disjoint bp.toNat 8 ((s.regs 4).toNat - 4128) 4152 ∧
    (z.toNat ≠ 0 →
      Buffer s z 32 false ∧ Outside z.toNat 32 R.rt ∧ Janus.Spec.Disjoint z.toNat 32 ((s.regs 4).toNat - 4128) 4152 ∧
      Janus.Spec.Disjoint z.toNat 32 bp.toNat 8 ∧
      (s.mem.readLE bp.toNat 8 ≠ 0 →
        Buffer s (BitVec.ofNat 64 (s.mem.readLE bp.toNat 8)) 32 true ∧
        Outside (s.mem.readLE bp.toNat 8) 32 R.rt ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 ((s.regs 4).toNat - 4128) 4152 ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 bp.toNat 8 ∧
        Janus.Spec.Disjoint (s.mem.readLE bp.toNat 8) 32 z.toNat 32 ∧
        (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
          Buffer s (BitVec.ofNat 64 (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8)) 32 true ∧
          Outside (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 R.rt ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 4).toNat - 4128) 4152 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 bp.toNat 8 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 z.toNat 32 ∧
          Janus.Spec.Disjoint (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 (s.mem.readLE bp.toNat 8) 32)))

/-- Extra separation facts of `correctness`: the goroutine's stack-guard slot is apart from the caller's writable blocks. -/
def PreX (z bp : BitVec 64) (s : State) : Prop :=
  Apart bp.toNat 8 ((s.regs 14).toNat + 16) 8 ∧
    (z.toNat ≠ 0 → s.mem.readLE bp.toNat 8 ≠ 0 →
      s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 < 2 ^ 63 ∧
      Apart (s.mem.readLE bp.toNat 8) 32 ((s.regs 14).toNat + 16) 8 ∧
      (4 ≤ s.mem.readLE (s.mem.readLE bp.toNat 8 + 24) 8 →
        Apart (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8) 32 ((s.regs 14).toNat + 16) 8))

/-- The postcondition of `correctness`. The return address at `[RSP]` is outside every range, so it is kept. -/
def Post (R : RtInv) (z bp : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → s'.mem.readLE bp.toNat 8 = 0) ∧
  (z.toNat ≠ 0 → ∃ P : Nat, BigOut s'.mem bp.toNat P (val256 s.mem z.toNat)) ∧
  MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
    (bp.toNat, bp.toNat + 8),
    (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
    (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) ∧
  (s.mem.readLE bp.toNat 8 = 0 →
    MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)]))


theorem ptr_of {s : State} {x n : Nat} {w : Bool} (hx : x < 2 ^ 64) (h : Buffer s (BitVec.ofNat 64 x) n w) :
    s.mem.accessible x n w = true ∧ x + n ≤ 2 ^ 48 := by
  obtain ⟨h1, h2⟩ := h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at h1 h2
  exact ⟨h2, h1⟩

/-- The pc after `*b` was loaded (or allocated) and stored: `mov (%rbx),%rcx` (`IntoBig+0x68`). -/
abbrev pcLoad : Nat := Extracted.entry + 0x68

/-- What every segment boundary state `S` has in common with the call state `s`: the frame (`RSP`, `RBP`,
the goroutine register, the saved frame pointer and the two spilled arguments) and the memory frame. -/
def Rel (R : RtInv) (z bp : BitVec 64) (s S : State) : Prop :=
  S.regs 4 = s.regs 4 - 24#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.regs 14 = s.regs 14 ∧
    S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧
    S.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = bp.toNat ∧
    MemFrame s.mem S.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
      (bp.toNat, bp.toNat + 8)])

theorem reaches_mono {p : Amd64.Program} {s : State} {Q Q' : Amd64.Outcome → Prop} (h : Reaches p s Q) (hQ : ∀ o, Q o → Q' o) :
    Reaches p s Q' := by
  obtain ⟨n, o, h1, h2⟩ := h
  exact ⟨n, o, h1, hQ o h2⟩

/-- From the tail's result (`BigOut` and a frame with the new block) to `Post`. -/
theorem post_of_tail (R : RtInv) (z bp : BitVec 64) (s : State) (P : Nat) (hz0 : z.toNat ≠ 0)
    (hn : s.mem.readLE bp.toNat 8 = 0 → ∀ a n,
      Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
        (bp.toNat, bp.toNat + 8)]) →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) :
    ∀ o : Amd64.Outcome,
      IsReturn (fun s' => ABIReturn s s' ∧ BigOut s'.mem bp.toNat P (val256 s.mem z.toNat) ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) o →
      (∀ a n, Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8),
          (s.mem.readLE bp.toNat 8, s.mem.readLE bp.toNat 8 + 32),
          (s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8, s.mem.readLE (s.mem.readLE bp.toNat 8 + 8) 8 + 32)]) →
        Outside a n (R.rt ++ [((s.regs 4).toNat - 4128, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 24),
          (bp.toNat, bp.toNat + 8), (P, P + 32)])) →
      IsReturn (fun s' => ABIReturn s s' ∧ Post R z bp s s') o := by
  intro o ho hw
  cases o with
  | returned s' => exact ⟨ho.1, fun h => absurd h hz0, fun _ => ⟨P, ho.2.1⟩, ho.2.2.mono hw, fun h0 => ho.2.2.mono (hn h0)⟩
  | stub n k s' => exact ho.elim

end Fv256.Amd64.IntoBig
