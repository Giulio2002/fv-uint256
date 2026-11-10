import Extracted
import Fv256.Spec.Format
import Fv256.Proofs.Common.FormatBridge
import Fv256.Spec.Arm64.Format
import Fv256.Proofs.Arm64.Format

/-!
# arm64: the compiled `(*uint256.Int).Format(s fmt.State, ch rune)` implements `Spec.format`  (`Fv256/Spec/Format.lean`)

`z.Format(s, ch)` is the `fmt.Formatter` of `uint256.Int`. Its specification (`Fv256.Spec.format`) in plain words:

* a nil receiver `z` makes one call `fmt.Fprint(s, "<nil>")` (the bytes `Spec.nilText`);
* otherwise, when `s` reports no width, no precision and none of the flags `+`, ` `, `-`, `0`, `#`, and the verb `ch` is one of
  `d`, `s`, `v`, `x` (`Spec.fastVerb`), exactly one call `s.Write(Spec.fastBytes ch x)` is made: the decimal digits of `x = *z`
  (`d`, `s`, `v`) or its lowercase hexadecimal digits without prefix (`x`);
* in every other case one call `(*big.Int).Format(s, ch)` on a big integer holding `x` is made.

`fmt.State`, `fmt.Fprint`, `io.Writer.Write` and `big.Int.Format` are interface/library calls of unknown code, so the claim is stated as
a CALL-HISTORY PROTOCOL: the interface answers (`Width`, `Precision`, `Flag`) and the calls the code makes are related by the call relations
`RW RP RF RWr RFp RBf` (an interface method is a relation `Res` between its arguments and results, as in `Janus.Contracts.ICall`). The
hypotheses `hWr`, `hFp`, `hBf` are the call-site obligations: whenever the code makes the `Write` call, its argument slice holds exactly
`Spec.fastBytes ch x` (`hWr`); the `Fprint` call is passed exactly `"<nil>"` (`hFp`); the big path is entered with `x` (`hBf`). The
`Post` says which of the three behaviours took place (`NilPost` / `FastPost` / `BigPost`, all machine-level, in
`Fv256/Spec/Arm64/FormatTransfer.lean`): `FastPost` asserts that the interface answered every query "plain" (`PlainHist`) and the verb is
`d`, `s`, `v` or `x`, and that `Write` was called; `BigPost` asserts that some query was answered "not plain" (or the verb is another
one) and that `Big.Format` was called with the right receiver and verb. Together with the obligations this is `Spec.format`.
Memory outside the runtime heap and the callee windows is untouched (the `MemFrame` conjuncts). The remaining hypotheses are the runtime
contracts (type assertion, allocation, `slicebytetostring`, write barriers) the Janus runtime model provides, and the `Res` relations
being callable at the addresses `fW fP fF fWr` of the interface's method table.
The proof is `Fv256/Proofs/Arm64/Format.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Fv256.FormatFastA64 Fv256.Arm64.FormatTransfer
open Janus.Spec.Type (IfaceModel)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Fv256.Arm64.Format

/-- The `Fprint` call-site obligation of the nil path: `fmt.Fprint(w, "<nil>")` with the receiver's data word `data` as `w` and a one-element
`[]any` holding the `string` `"<nil>"` (its bytes are `Spec.nilText`). -/
def PrintsNil (data : BitVec 64) (sc : State) : Prop :=
  sc.regs 1 = data ∧ sc.regs 3 = 1#64 ∧ sc.regs 4 = 1#64 ∧ (sc.regs 2).toNat = sc.sp.toNat + 56 ∧
  sc.mem.readLE (sc.regs 2).toNat 8 = Fv256.Arm64.FormatNil.strTyA ∧ sc.mem.readLE ((sc.regs 2).toNat + 8) 8 = Fv256.Arm64.FormatNil.hdrA ∧
  sc.mem.readLE Fv256.Arm64.FormatNil.hdrA 8 = Fv256.Arm64.FormatNil.litA ∧ sc.mem.readLE (Fv256.Arm64.FormatNil.hdrA + 8) 8 = 5 ∧ StrOut sc.mem Fv256.Arm64.FormatNil.litA 5 Fv256.Spec.nilText

/-- PRECONDITION (machine facts): the standard Go call state (stack check, frame, alignment), the layout of the runtime-owned memory `rt`,
and, for a nil receiver, the facts the type assertion `s.(io.Writer)` needs; for a non-nil receiver the interface method table (`tab`) holding the
code pointers `fW fP fF fWr` of `Width`, `Precision`, `Flag`, `Write`, the readable `*z` (= `zv`), and the runtime allocator state. -/
def Pre (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat)) (stack b0 fW fP fF fWr zv : Nat) (z tab data : BitVec 64) (s : State) : Prop :=
  PreF R H R2 rt stack b0 fW fP fF fWr zv z tab data s

/-- POSTCONDITION (call-history protocol, see the header): a nil receiver ended with the `Fprint` call (`NilPost`); a non-nil receiver ended
either on the fast path (`FastPost`: every query plain and verb `d`/`s`/`v`/`x`, then the one `Write` call whose bytes the obligation `hWr`
fixes to `Spec.fastBytes ch x`) or on the big path (`BigPost`: some query not plain or another verb, then the one `big.Int.Format` call);
memory is framed in each case. -/
def Post (R : IfaceModel) (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF : Nat) (RW RP RF RWr RFp RBf : Res) (z tab data ch : BitVec 64) (s s' : State) : Prop :=
  (z.toNat = 0 → NilPost R rt stack RFp tab data s s') ∧
      (z.toNat ≠ 0 → FastPost rt stack fW fP fF RW RP RF RWr data ch s s' ∨
        BigPost R2 rt stack fW fP fF RW RP RF RBf tab data ch s s')

/-- THE CLAIM: for every runtime and interface obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed)
in a state meeting `Post`. -/
theorem correctness (impl : List Janus.Segment) (hI : ImplApart Extracted.program impl)
    (R : IfaceModel) (hl : R.Laws) (H : Janus.Contracts.RtReady)
    (hta : Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H)
    (R2 : RtInv)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R2)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2)
    (rt : List (Nat × Nat))
    (hss : RtContract (Extracted.program.ofImpl impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hst : RtContract (Extracted.program.ofImpl impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (fW fP fF fWr stack b0 zv : Nat) (RW RP RF RWr RFp RBf : Res)
    (h4608 : 4608 ≤ stack)
    (z tab data ch : BitVec 64)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True) (RtPreserves R2))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True) (RtPreserves R2))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
      (FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) zv)))
    (hFp : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 stack 80 rt (fun _ => [])
      RFp (PrintsNil data))
    (hBf : ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 stack 120 rt (fun _ => [])
      RBf (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P zv ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, tab, data, ch]
      (Pre R H R2 rt stack b0 fW fP fF fWr zv z tab data) (Post R R2 rt stack fW fP fF RW RP RF RWr RFp RBf z tab data ch) :=
  correctness_proof impl hI R hl H hta R2 hnew hwb1 hwb2 rt hss hst fW fP fF fWr stack b0 zv RW RP RF RWr RFp RBf h4608 z tab data ch hW hP hF (by rw [Fv256.FormatBridge.fastBytes_eq]; exact hWr) hFp hBf

namespace Witness

/-- The fast path (`z = 16`, verb `d`, every query answered plain): all hypotheses of `correctness`, the toy runtime and callees, and the
precondition hold together. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 16)) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (PrintsNil data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    Pre R H R2 rt 4608 0x400 fa fa fa fa 16 z tab data s ) ∧
    ((∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.Arm64.CallSites.NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 16)) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (PrintsNil data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 rt 4608 fa fa fa Rc Rc Rc Rc Rd Rd z tab data ch s s' := by
  have h := Witness.nonvacuous_proof
  simp only [Fv256.FormatBridge.fastBytes_eq] at h
  exact h

/-- The nil receiver (`z = 0`). -/
theorem nil : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 0)) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (PrintsNil data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    Pre R H R2 rt 4608 0x400 fa fa fa fa 0 z tab data s ) ∧
    ((∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.Arm64.CallSites.NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 0)) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (PrintsNil data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 0 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 rt 4608 fa fa fa Rc Rc Rc Rc Rd Rd z tab data ch s s' := by
  have h := Witness.nil_proof
  simp only [Fv256.FormatBridge.fastBytes_eq] at h
  exact h

/-- The big path (`z = 16`, the callees answer "has width"): the toy allocator `R2` is satisfiable and serves `IntoBig`'s requests. -/
theorem big : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608 ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 16)) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (PrintsNil data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    Pre R H R2 rt 4608 0x400 fa fa fa fa 16 z tab data s ∧
    NotPlain Rc Rc Rc data fa fa fa ch (ch.toNat % 2 ^ 32) ∧
    (∃ (P : Nat) (j0 j1 j2 : BitVec 64), Rd (BitVec.ofNat 64 P) tab data
      (BitVec.ofNat 64 (if ch.toNat % 2 ^ 32 < 2 ^ 31 then ch.toNat % 2 ^ 32 else ch.toNat % 2 ^ 32 + 18446744069414584320)) j0 j1 j2) ) ∧
    ((∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.typeAssert") ∧ Fv256.Arm64.FormatCS.TypeAssertSite R H s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.Arm64.CallSites.NewobjectLiveSite R2 (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.Arm64.CallSites.WbLiveSite R2 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.stringtoslicebyte") ∧ RtPre rt 4096 H stringtoslicebyteSpec s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 1 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 2 4608 120 rt (fun _ => True) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 fa ∧ ICallPre 4 4608 120 rt (Fv256.FormatFastA64.FastWP data (Fv256.Spec.fastBytes (ch.toNat % 2 ^ 32) 16)) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint") ∧ ICallPre 5 4608 80 rt (PrintsNil data) s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format") ∧ ICallPre 4 4608 120 rt (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧ (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s_c)) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 rt 4608 fa fa fa Rc Rc Rc Rc Rd Rd z tab data ch s s' := by
  have h := Witness.big_proof
  simp only [Fv256.FormatBridge.fastBytes_eq] at h
  exact h

end Witness

end Fv256.Arm64.Format
