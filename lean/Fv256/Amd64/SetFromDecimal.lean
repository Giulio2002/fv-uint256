import Extracted
import Fv256.Spec.SetFromDecimal
import Fv256.Spec.Amd64.SfdTopCfg
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Amd64.Machine
import Fv256.Proofs.Common.SfdBridge
import Fv256.Proofs.Amd64.SetFromDecimal
import Fv256.Spec.Amd64.CallSites.Live

/-!
# amd64: the compiled `(*uint256.Int).SetFromDecimal` implements `Spec.setFromDecimal`  (`Fv256/Spec/SetFromDecimal.lean`)

`z.SetFromDecimal(s)` parses the decimal string `s` into `z` exactly as `Fv256.Spec.setFromDecimal` says: the number (leading `+`
and zeros allowed, at most `2^256 - 1`), `io.EOF` for an empty digit string, `ErrBig256Range` for a too large one, or a
`strconv` syntax error naming the offending 19-digit chunk. The call never faults or panics. The proof is
`Fv256/Proofs/Amd64/SetFromDecimal.lean`; the hypotheses `hif ... hcmp` assume the runtime helpers (allocator, write barriers, `memmove`,
`cmpstring`, interface equality) behave as their contracts.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Janus.Contracts.EqHashModel Fv256.Amd64.SfdTopSpec Fv256.Amd64.SfdTopCfg
  Janus.Contracts.Toy Janus.Contracts.IfaceModel

open Fv256.CallSites

namespace Fv256.Amd64.SetFromDecimal

/-- PRECONDITION of `SetFromDecimal(z, s)`: `z` in `RAX`, the string pointer in `RBX`, its length in `RCX`; the standard runtime model (`R`: allocator, `R2`: interface model),
the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, the multiplier table, the 78-digit bound string)
and the chunk-copy facts for the error path. The runtime-contract
hypotheses (below) say the runtime stubs behave as their contracts. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  TopPre0 extCfg R R2 T b L lo hi z pS nS s

open Fv256.C in
/-- POSTCONDITION: callee-saved state is preserved (`Kept`), and the outcome is exactly the one `Fv256.Spec.setFromDecimal` gives for the bytes of the
string `s` (read BEFORE the call):
* `ok v`: `err = nil` (both result registers zero), `z` now holds `v`, only `z[0, 32)` and the stack window were written;
* `eof`: `err` is the package variable `io.EOF`, `z` is `0`;
* `range`: `err` is `ErrBig256Range`, `z` is unchanged;
* `badSyntax`: `err` is a freshly allocated `*strconv.NumError{Func: "ParseUint", Num: <chunk>, Err: ErrSyntax}` whose `Num` is
  the copied chunk `s[lo', lo' + len')` (the claim says nothing about `z`; memory changes are confined to the runtime heap and `z`). -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : Prop :=
  Kept s s' ∧
  match Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) with
  | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v ∧ Env extCfg R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .eof =>
      (s'.regs 0).toNat = s.mem.readLE extCfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (extCfg.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0 ∧ Env extCfg R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .range =>
      (s'.regs 0).toNat = s.mem.readLE extCfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (extCfg.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat ∧ Env extCfg R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .badSyntax lo' len' =>
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 extCfg.numErrItab ∧ s'.regs 3 = t ∧
        TeObj extCfg R b L (BitVec.ofNat 64 extCfg.fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition `TopPost`, which speaks of `decParse`, is equivalent to `Post`.
`decParse` agrees with `Spec.setFromDecimal` by `Fv256.SfdBridge.decParse_eq`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : TopPost extCfg R R2 T b L lo hi z pS nS s s' ↔ Post R R2 T b L lo hi z pS nS s s' := by
  unfold TopPost Post
  rw [Fv256.SfdBridge.decParse_eq, Fv256.SfdBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) = r
  apply and_congr_right
  intro _
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax] <;>
    exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ => h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a
state meeting `Post`. -/
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (Pre R R2 T b L lo hi z pS nS) (Post R R2 T b L lo hi z pS nS) :=
  (correctness_proof impl R R2 T b L lo hi z pS nS hif hnew hmg hmv hwb1 hwb2 hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi z pS nS s s').1 hq)

namespace Witness

/-- The hypotheses of `correctness` hold together: a runtime (`impl`, `R`, `R2`), a budget, a stack window and a call of
`SetFromDecimal(z, s)` for a 45-digit decimal `s` (three chunks of 19, 19 and 7 digits: the multi-word multiply/accumulate path) satisfying the precondition. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64) (ret : Nat) (s : State),
    Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    Pre R R2 T b L lo hi z pS nS s ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi z pS nS s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pS, nS, ret, s, h⟩ := Wit.nonvacuous
  refine ⟨impl, R, R2, T, b, L, lo, hi, z, pS, nS, ret, s, ?_⟩
  revert h
  repeat' refine And.imp id ?_
  intro hret
  exact hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi z pS nS s s').1 hq⟩

end Witness

end Fv256.Amd64.SetFromDecimal
