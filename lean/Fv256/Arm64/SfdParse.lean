import Fv256.Spec
import Fv256.Util
import Fv256.HexLemmas
import Fv256.SpecI
import Fv256.UtilI
import Fv256.Arm64.SfdProg

/-!
# `internal/strconv.ParseUint(s, 10, 64)` on a string of 1 to 19 bytes (arm64)

The digit loop of `strconv.ParseUint` for `base = 10`, `bitSize = 64`: for at most 19 bytes the value cannot overflow
(`10^19 - 1 < 2^64`), so the result is the number when every byte is an ASCII digit, and the internal syntax error
otherwise.  The error values are the addresses of the constant `internal/strconv.Error` objects in read-only data
(`ErrSyntax` is the constant at `0xf5940`).  Over the library program `SfdProg.program`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.I

namespace Fv256.Arm64.SfdParse

abbrev ip : Nat := segAddr Fv256.Arm64.SfdProg.program "internal/strconv.ParseUint"
abbrev head : Nat := ip + 0x1bc

/-- the address of the `internal/strconv.ErrSyntax` constant (an `internal/strconv.Error`) -/
abbrev synAddr : Nat := 0xf5940
/-- the itab of `internal/strconv.Error` as an `error` -/
abbrev errItab : Nat := 0xf6920

def LoopQ (s : State) (M : Memory) (p len : Nat) (s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧ s'.mem = M ∧
  ((allDec (Fv256.C.bytesAt M p) 0 len ∧ (s'.regs 0).toNat = decSum (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∨
   (¬ allDec (Fv256.C.bytesAt M p) 0 len ∧ s'.regs 0 = 0 ∧ (s'.regs 1).toNat = errItab ∧ (s'.regs 2).toNat = synAddr))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem loop (impl : List Segment) (s : State) (M : Memory) (p len : BitVec 64)
    (hL : 1 ≤ len.toNat) (hL2 : len.toNat ≤ 19)
    (hsa : M.accessible p.toNat len.toNat false = true) (hp : p.toNat + len.toNat ≤ 2 ^ 48)
    (hrM : M.readLE (s.sp.toNat - 48) 8 = (s.regs 30).toNat) (hbp : M.readLE (s.sp.toNat - 56) 8 = (s.regs 29).toNat)
    (hl1 : (s.regs 30).toNat % 4 = 0) (hl2 : (s.regs 30).toNat < 2 ^ 48)
    (hsp : 56 ≤ s.sp.toNat) (hspa : s.sp.toNat + 16 ≤ 2 ^ 48)
    (hacc : M.accessible (s.sp.toNat - 56) (56 + 16) true = true) :
    ∀ n (S : State) (i : Nat), n = len.toNat - i → i ≤ len.toNat →
      S.pc = BitVec.ofNat 64 head → S.regs 8 = BitVec.ofNat 64 i → S.regs 5 = len →
      S.regs 4 = p → S.regs 9 = BitVec.ofNat 64 (decSum (Fv256.C.bytesAt M p.toNat) 0 i) →
      S.regs 7 = 0x199999999999999a#64 → S.regs 6 = 10#64 → S.regs 3 = 0xffffffffffffffff#64 →
      S.regs 2 = 10#64 → S.regs 10 = 0#64 → S.sp = s.sp - 48#64 → S.regs 29 = s.sp - 8#64 - 48#64 →
      S.regs 30 = s.regs 30 → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.mem = M →
      allDec (Fv256.C.bytesAt M p.toNat) 0 i →
      ReachesRet (Fv256.Arm64.SfdProg.program.link impl) (s.regs 30) S (LoopQ s M p.toNat len.toNat) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i hn hi hpc h8 h5 h4 h9 h7 h6 h3 h2 h10 hsS h29 h30 h28 h18 hmem hdig
    by_cases hlt : i < len.toNat
    all_goals janus_run until [head]
    all_goals sorry
