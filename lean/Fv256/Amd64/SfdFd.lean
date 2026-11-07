import Fv256.Amd64.SfdProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SumC64
import Fv256.Amd64.SfdEnv
import Fv256.Amd64.SfdTePre
import Fv256.Amd64.SfdBridge
import Fv256.Amd64.SfdPw
import Fv256.Amd64.SfdMul

/-!
# `(*Int).fromDecimal(bs string) error` (amd64)

The chunk loop of `SetFromDecimal`: up to five calls of `strconv.ParseUint(chunk, 10, 64)` on 19-digit chunks from the
least significant end, each multiplied by the proper power of ten (`Mul` with the `multipliers` table) and added to `z`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I

namespace Fv256.Amd64.SfdFd

abbrev fd : Nat := segAddr Fv256.Amd64.SfdProg.program "github.com/holiman/uint256.(*Int).fromDecimal"
abbrev mulTab : Nat := Fv256.Amd64.SfdProg.dataAddr.«github.com/holiman/uint256.multipliers»
abbrev ioEOF : Nat := Fv256.Amd64.SfdProg.dataAddr.«io.EOF»

/-- the package variable `multipliers = [5]*Int{nil, 10^19, 10^38, 10^57, 10^76}` as memory holds it: the table, and the
four `Int`s it points to, are readable, hold the powers of ten, and lie outside `z`'s buffer and the stack window. -/
def MultOK (z lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.accessible mulTab 40 false = true ∧ Outside mulTab 40 [(lo, hi), (z, z + 32)] ∧
  ∀ k, 1 ≤ k → k ≤ 4 →
    m.accessible (m.readLE (mulTab + 8 * k) 8) 32 false = true ∧ m.readLE (mulTab + 8 * k) 8 + 32 ≤ 2 ^ 48 ∧
    Janus.Spec.val256 m (m.readLE (mulTab + 8 * k) 8) = 10 ^ (19 * k) ∧
    Outside (m.readLE (mulTab + 8 * k) 8) 32 [(lo, hi), (z, z + 32)]

theorem MultOK.frame {z lo hi : Nat} {m m' : Janus.Arm64.Memory} (h : MultOK z lo hi m)
    (hf : MemFrame m m' [(lo, hi), (z, z + 32)]) : MultOK z lo hi m' := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : ∀ k, 1 ≤ k → k ≤ 4 → m'.readLE (mulTab + 8 * k) 8 = m.readLE (mulTab + 8 * k) 8 := by
    intro k hk1 hk2
    exact hf.readLE _ _ (Outside.of_sub h2 (by omega) (by omega))
  refine ⟨by rw [hf.accessible]; exact h1, h2, fun k hk1 hk2 => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h3 k hk1 hk2
  rw [e k hk1 hk2]
  refine ⟨by rw [hf.accessible]; exact a1, a2, ?_, a4⟩
  rw [← a3]
  unfold Janus.Spec.val256
  exact hf.readLE _ _ a4


open Fv256.C in
/-- every chunk `(sp, sl)` of the string `(pS, nS)` that `fromDecimal` hands to `strconv.ParseUint` meets the facts
`strconv.toError` needs for it (budget, runtime requests, readability, apartness from the window). -/
def ChunkAll (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (pS nS : Nat) (lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  ∀ sp sl : Nat, pS ≤ sp → sp + sl ≤ pS + nS → 1 ≤ sl → sl ≤ 19 →
    ChunkOK R R2 L b (BitVec.ofNat 64 sp) (BitVec.ofNat 64 sl) lo hi m

open Fv256.C in
def FdPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = pS ∧ s.regs 1 = nS ∧ nS.toNat ≤ 78 ∧ Mod R R2 T L ∧
  Env R R2 T b L lo hi s ∧ lo + 4432 ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 32 ≤ hi ∧
  MultOK z.toNat lo hi s.mem ∧ s.mem.accessible ioEOF 16 false = true ∧ Outside ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  Buffer s z 32 true ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  Outside z.toNat 32 R2.priv ∧ (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 14).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 14).toNat + 16) ∧
  (pS.toNat + nS.toNat ≤ 2 ^ 48 ∧ (nS.toNat = 0 ∨ s.mem.accessible pS.toNat nS.toNat false = true)) ∧ (nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (nS.toNat = 0 ∨ pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat) ∧
  ChunkAll R R2 L b pS.toNat nS.toNat lo hi s.mem ∧
  (allDec (bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)

open Fv256.C in
def FdPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧
  ((fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0 ∧ Env R R2 T b L lo hi s' ∧ MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (∃ v, fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v ∧ Env R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (∃ lo' len', fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 numErrItab ∧ s'.regs 3 = t ∧
        TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])))

end Fv256.Amd64.SfdFd
