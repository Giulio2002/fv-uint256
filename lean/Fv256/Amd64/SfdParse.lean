import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.HexLemmas
import Fv256.SpecI

/-!
# `internal/strconv.ParseUint(s, 10, 64)` on a string of 1 to 19 bytes (amd64)

The digit loop of `strconv.ParseUint` for `base = 10`, `bitSize = 64`: for at most 19 bytes the value cannot overflow
(`10^19 - 1 < 2^64`), so the result is the number when every byte is an ASCII digit, and the internal syntax error
otherwise.  The error values are the addresses of the constant `internal/strconv.Error` objects in read-only data
(`ErrSyntax` is the constant at `dataAddr.«.rodata#9967e7a3»`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.I

namespace Fv256.Amd64.SfdParse

abbrev ip : Nat := segAddr Extracted.program "internal/strconv.ParseUint"
abbrev head : Nat := ip + 0x1b0

/-- the address of the `internal/strconv.ErrSyntax` constant (an `internal/strconv.Error`) -/
abbrev synAddr : Nat := Extracted.dataAddr.«.rodata#9967e7a3»
/-- the itab of `internal/strconv.Error` as an `error` -/
abbrev errItab : Nat := Extracted.dataAddr.«go:itab.internal/strconv.Error,error»

def LoopQ (s : State) (M : Memory) (p len : Nat) (s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧ s'.mem = M ∧
  ((allDec (Fv256.C.bytesAt M p) 0 len ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 3 = 0 ∧ s'.regs 1 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 0 = 0 ∧ (s'.regs 3).toNat = errItab ∧ (s'.regs 1).toNat = synAddr))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem loop (impl : List Janus.Amd64.Segment) (s : State) (M : Memory) (p len : BitVec 64)
    (hL : 1 ≤ len.toNat) (hL2 : len.toNat ≤ 19)
    (hsa : M.accessible p.toNat len.toNat false = true) (hp : p.toNat + len.toNat ≤ 2 ^ 48)
    (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ n (S : State) (i : Nat), n = len.toNat - i → i ≤ len.toNat →
      S.rip = BitVec.ofNat 64 head → S.regs 1 = BitVec.ofNat 64 i → S.regs 6 = len →
      S.regs 10 = p → S.regs 11 = BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) →
      S.regs 2 = 0x199999999999999a#64 → S.regs 8 = 10#64 → S.regs 7 = 0xffffffffffffffff#64 →
      S.regs 0 = 10#64 → S.regs 12 = 0#64 → S.regs 4 = s.regs 4 - 0x20#64 → S.regs 5 = s.regs 4 - 8#64 →
      S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 → S.df = s.df → S.fsBase = s.fsBase → S.mem = M →
      allDec (Fv256.C.bytesAt M p.toNat) 0 i →
      ReachesRet (Extracted.program.link impl) (retAddrOf s) S (LoopQ s M p.toNat len.toNat) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i hn hi hpc h1 h6 h10 h11 h2 h8 h7 h0 h12 h4 h5 h14 hx15 hdf hfs hmem hdig
    sorry

end Fv256.Amd64.SfdParse
