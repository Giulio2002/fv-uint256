import Fv256.Spec
import Fv256.Util
import Fv256.SpecI
import Fv256.UtilI
import Fv256.SfdFdMath
import Fv256.SfdFdLem
import Fv256.Arm64.SfdProg
import Fv256.Arm64.SfdEnv
import Fv256.Arm64.SfdTePre
import Fv256.Arm64.SfdPw
import Fv256.Arm64.SfdMul

/-!
# `(*Int).fromDecimal(bs string) error` (arm64): STATEMENT (library program `SfdProg.program`)

The chunk loop of `SetFromDecimal`: up to five calls of `strconv.ParseUint(chunk, 10, 64)` on 19-digit chunks from the
least significant end, each multiplied by the proper power of ten (`Mul` with the `multipliers` table) and added to `z`.
Registers: in `X0 = z`, `X1 = pS`, `X2 = nS`; out `X0, X1 = err` (nil: both 0).  Frame 160 bytes below the entry `SP`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdEnv Fv256.Arm64.SfdToError Fv256.Arm64.SfdPw

namespace Fv256.Arm64.SfdFd

abbrev fd : Nat := segAddr Fv256.Arm64.SfdProg.program "github.com/holiman/uint256.(*Int).fromDecimal"
/-- the package variable `multipliers` (five pointers: `nil, 10^19, 10^38, 10^57, 10^76`) -/
abbrev mulTab : Nat := 0x1b6540
/-- the package variable `io.EOF` (an `error` interface: two words) -/
abbrev ioEOF : Nat := 0x1b5c10

def MultOK (z lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.accessible mulTab 40 false = true ∧ Outside mulTab 40 [(lo, hi), (z, z + 32)] ∧
  ∀ k, 1 ≤ k → k ≤ 4 →
    m.accessible (m.readLE (mulTab + 8 * k) 8) 32 false = true ∧ m.readLE (mulTab + 8 * k) 8 + 32 ≤ 2 ^ 48 ∧
    Janus.Spec.val256 m (m.readLE (mulTab + 8 * k) 8) = 10 ^ (19 * k) ∧
    Outside (m.readLE (mulTab + 8 * k) 8) 32 [(lo, hi), (z, z + 32)]

open Fv256.C in
def ChunkAll (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (b : Nat) (pS nS : Nat) (lo hi : Nat) (m : Janus.Arm64.Memory) : Prop :=
  ∀ sp sl : Nat, pS ≤ sp → sp + sl ≤ pS + nS → 1 ≤ sl → sl ≤ 19 →
    ChunkOK R R2 L b (BitVec.ofNat 64 sp) (BitVec.ofNat 64 sl) lo hi m

open Fv256.C in
def FdPre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 48 ∧
  s.regs 0 = z ∧ s.regs 1 = pS ∧ s.regs 2 = nS ∧ nS.toNat ≤ 78 ∧ Mod R R2 T L ∧
  Env R R2 T b L lo hi s ∧ lo + 4440 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ hi ∧
  MultOK z.toNat lo hi s.mem ∧ s.mem.accessible ioEOF 16 false = true ∧ Outside ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] ∧
  Ptr32 s.mem z true ∧ (z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat) ∧ (Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L) ∧
  Outside z.toNat 32 R2.priv ∧ (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]) ∧
  ((s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16) ∧
  s.mem.accessible pS.toNat nS.toNat false = true ∧ pS.toNat + nS.toNat ≤ 2 ^ 48 ∧ (pS.toNat + nS.toNat ≤ lo ∨ hi ≤ pS.toNat) ∧
  (pS.toNat + nS.toNat ≤ z.toNat ∨ z.toNat + 32 ≤ pS.toNat) ∧
  ChunkAll R R2 L b pS.toNat nS.toNat lo hi s.mem ∧
  (allDec (bytesAt s.mem pS.toNat) 0 nS.toNat → decSum (bytesAt s.mem pS.toNat) 0 nS.toNat < 2 ^ 256)

open Fv256.C in
/-- the two words at `sp - 8` and `sp` (the caller's saved FP/LR) are unchanged -/
def Keep (s0 S : State) : Prop :=
  S.mem.readLE (s0.sp.toNat - 8) 8 = s0.mem.readLE (s0.sp.toNat - 8) 8 ∧ S.mem.readLE s0.sp.toNat 8 = s0.mem.readLE s0.sp.toNat 8

open Fv256.C in
def FdPost (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧ Keep s s' ∧
  ((fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .eof ∧
      (s'.regs 0).toNat = s.mem.readLE ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0 ∧ Env R R2 T b L lo hi s' ∧ MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (∃ v, fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .ok v ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v ∧ Env R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]) ∨
   (∃ lo' len', fromDec (bytesAt s.mem pS.toNat) nS.toNat 0 = .syntax lo' len' ∧
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 numErrItab ∧ s'.regs 1 = t ∧
        TeObj R b L (BitVec.ofNat 64 fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])))

def FdSum (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)
    (z pS nS : BitVec 64) : Prop :=
  Summary (Fv256.Arm64.SfdToError.P.link impl) fd (FdPre R R2 T b L lo hi z pS nS) (FdPost R R2 T b L lo hi z pS nS)

end Fv256.Arm64.SfdFd
