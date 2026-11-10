import Extracted
import Fv256.Spec.SetFromDecimal
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.SfdCfgE
import Fv256.Arm64.Machine
import Fv256.Proofs.Common.SfdBridge
import Fv256.Proofs.Arm64.SetFromDecimal
import Fv256.Spec.Arm64.CallSites.Base

/-!
# arm64: the compiled `(*uint256.Int).SetFromDecimal` implements `Spec.setFromDecimal`  (`Fv256/Spec/SetFromDecimal.lean`)

`z.SetFromDecimal(s)` parses the decimal string `s` into `z` exactly as `Fv256.Spec.setFromDecimal` says: the number (leading `+`
and zeros allowed, at most `2^256 - 1`), `io.EOF` for an empty digit string, `ErrBig256Range` for a too large one, or a
`strconv` syntax error naming the offending 19-digit chunk. The call never faults or panics. The proof is
`Fv256/Proofs/Arm64/SetFromDecimal.lean`; the hypotheses `hif ... hcmp` assume the runtime helpers (allocator, write barriers, `memmove`,
`cmpstring`, interface equality) behave as their contracts.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
  Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.SetFromDecimal

/-- PRECONDITION of `SetFromDecimal(z, s)`: `z` in `X0`, the string pointer in `X1`, its length in `X2`; the standard runtime model (`R`: allocator, `R2`: interface model),
the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, the multiplier table, the 78-digit bound string)
and the chunk-copy facts for the error path. The runtime-contract
hypotheses (below) say the runtime stubs behave as their contracts. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s : State) : Prop :=
  TopPre cfgE R R2 T b L lo hi z pS nS s

open Fv256.C in
/-- POSTCONDITION: the stack pointer and callee-saved registers `X29`, `X28`, `X18` are preserved, and the outcome is exactly the one `Fv256.Spec.setFromDecimal` gives for the bytes of the
string `s` (read BEFORE the call):
* `ok v`: `err = nil` (both result registers zero), `z` now holds `v`, only `z[0, 32)` and the stack window were written;
* `eof`: `err` is the package variable `io.EOF`, `z` is `0`;
* `range`: `err` is `ErrBig256Range`, `z` is unchanged;
* `badSyntax`: `err` is a freshly allocated `*strconv.NumError{Func: "ParseUint", Num: <chunk>, Err: ErrSyntax}` whose `Num` is
  the copied chunk `s[lo', lo' + len')` (the claim says nothing about `z`; memory changes are confined to the runtime heap and `z`). -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : Prop :=
  s'.sp = s.sp ∧ s'.regs 29 = s.regs 29 ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 18 = s.regs 18 ∧
  s'.mem.readLE (s.sp.toNat - 8) 8 = s.mem.readLE (s.sp.toNat - 8) 8 ∧ s'.mem.readLE s.sp.toNat 8 = s.mem.readLE s.sp.toNat 8 ∧
  match Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) with
  | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v ∧ Env cfgE R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .eof =>
      (s'.regs 0).toNat = s.mem.readLE cfgE.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfgE.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0 ∧ Env cfgE R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .range =>
      (s'.regs 0).toNat = s.mem.readLE cfgE.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfgE.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat ∧ Env cfgE R R2 T b L lo hi s' ∧
      MemFrame s.mem s'.mem [(lo, hi), (z.toNat, z.toNat + 32)]
  | .badSyntax lo' len' =>
      ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 cfgE.numErrItab ∧ s'.regs 1 = t ∧
        TeObj cfgE R b L (BitVec.ofNat 64 cfgE.fnStr) 9#64 (BitVec.ofNat 64 (pS.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧
        MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition `TopPost`, which speaks of `decParse`, is equivalent to `Post`.
`decParse` agrees with `Spec.setFromDecimal` by `Fv256.SfdBridge.decParse_eq`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64)
    (s s' : State) : TopPost cfgE R R2 T b L lo hi z pS nS s s' ↔ Post R R2 T b L lo hi z pS nS s s' := by
  unfold TopPost Post
  rw [Fv256.SfdBridge.decParse_eq, Fv256.SfdBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) = r
  iterate 6 (apply and_congr_right; intro _)
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax] <;>
    exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ => h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a
state meeting `Post`. -/
theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pS, nS]
      (Pre R R2 T b L lo hi z pS nS) (Post R R2 T b L lo hi z pS nS) :=
  (correctness_proof impl R R2 T b L lo hi z pS nS hI hif hnew hmg hmv hwb1 hwb2 hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi z pS nS s s').1 hq)

namespace Witness

/-- Non-vacuity: a concrete runtime (stub code at the contract addresses, toy allocator `R`, interface model `R0`), a stack
window and a call `SetFromDecimal(z, "7")` satisfy EVERY hypothesis of `correctness` (the `ImplApart` premise, the seven runtime
contracts, the call setup) and its precondition `TopPre` (the model law `hT`, the static objects, the multiplier table, the
chunk facts). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pS nS : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    Pre R R2 T b L lo hi z pS nS s ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi z pS nS s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pS, nS, ret, s, h⟩ := Wit.nonvacuous
  refine ⟨impl, R, R2, T, b, L, lo, hi, z, pS, nS, ret, s, ?_⟩
  revert h
  repeat' refine And.imp id ?_
  intro hret
  exact hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi z pS nS s s').1 hq⟩

end Witness

end Fv256.Arm64.SetFromDecimal
