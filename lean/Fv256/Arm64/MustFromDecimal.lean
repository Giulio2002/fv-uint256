import Extracted
import Fv256.Spec.MustFromDecimal
import Fv256.Spec.Arm64.MustFromDecimal
import Fv256.Spec.Arm64.MFdWitC
import Fv256.Spec.I
import Fv256.Proofs.Common.SfdBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.MustFromDecimalMain

/-!
# arm64: the compiled `uint256.MustFromDecimal` implements `Spec.mustFromDecimal`  (`Fv256/Spec/MustFromDecimal.lean`)

`MustFromDecimal(s)` (`X0`, `X1` = `s.ptr`, `s.len`) never faults. For the bytes of `s` it does what `Fv256.Spec.mustFromDecimal` says: if the
string is a valid decimal number it RETURNS a pointer to a fresh 32-byte `Int` in the runtime's heap holding the number; otherwise it
PANICS with the error value (`io.EOF`, `ErrBig256Range`, or a freshly allocated `*strconv.NumError`). `P` is the panic runtime (how a
panic is classified). The hypotheses `hif ... hcmp` assume the runtime helpers behave as their contracts.
The proof is `Fv256/Proofs/Arm64/MustFromDecimalMain.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel Janus.Contracts.Panic Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.CallSites

open Fv256.Arm64.MustFromDecimal

namespace Fv256.Arm64.MustFromDecimal

/-- PRECONDITION (machine facts only): the standard runtime model (`R`: allocator, `R2`: interface model), the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, their type words, the multiplier table, the 78-digit bound string), the string `s` readable and outside the window, and the chunk-copy facts for the error path; the static data is loaded. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Arm64.MustFromDecimal.PreFd R R2 T b L lo hi pS nS s

/-- POSTCONDITION when the call RETURNS: `Spec.mustFromDecimal` yields `ok v` (the string is valid), and the result pointer addresses a 32-byte block inside the heap holding `v`; only the heap and the window were written. -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.mustFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) with
   | .ok v =>
      ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v
   | _ => False) ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])

/-- POSTCONDITION when the call PANICS: `Spec.mustFromDecimal` yields `eof`, `range` or `badSyntax`: the panic value is the corresponding error interface value (`io.EOF`, `ErrBig256Range`, or a pointer to a fresh `*strconv.NumError` inside the heap). -/
def Panics (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) (v : Janus.Eface) (_ : State) : Prop :=
  match Fv256.Spec.mustFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) with
  | .ok _ => False
  | .eof => v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩
  | .range => v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩
  | .badSyntax _ _ => ∃ t : Nat, InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition is equivalent to `Post`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s s' : State) :
    ((∃ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v) ∧
            (∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
              ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v) ∧
            MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])) ↔ Post R R2 T b L lo hi pS nS s s' := by
  unfold Post Fv256.Spec.mustFromDecimal Fv256.Spec.fromDecimal
  rw [Fv256.SfdBridge.decParse_eq, Fv256.SfdBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) = r
  rw [← and_assoc]
  apply and_congr_left
  intro _
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax]

/-- BRIDGE (not part of the claim): the implementation-shaped panic condition is equivalent to `Panics`. -/
theorem pan_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) (v : Janus.Eface) (s2 : State) :
    ((decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof ∧
              v = ⟨s.mem.readLE (s.mem.readLE cfg.ioEOF 8 + 8) 8, s.mem.readLE (cfg.ioEOF + 8) 8⟩) ∨
            (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range ∧
              v = ⟨s.mem.readLE (s.mem.readLE cfg.errBig 8 + 8) 8, s.mem.readLE (cfg.errBig + 8) 8⟩) ∨
            (∃ lo' len' t : Nat, decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' ∧
              InRanges t (blockSize 48 false) R.rt ∧ v = ⟨s.mem.readLE (cfg.numErrItab + 8) 8, t⟩)) ↔ Panics R R2 T b L lo hi pS nS s v s2 := by
  unfold Panics Fv256.Spec.mustFromDecimal Fv256.Spec.fromDecimal
  rw [Fv256.SfdBridge.decParse_eq, Fv256.SfdBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) = r
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax]

/-- THE CLAIM: for every panic runtime `P`, every runtime obeying the contracts and every call meeting `Pre`, the compiled code either returns in a state meeting `Post` or panics with a value meeting `Panics`, never faulting. -/
theorem correctness (P : Janus.Spec.PanicRuntime) (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (pS nS : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    EnsuresGo (Extracted.program.link impl) Extracted.entry [pS, nS]
      (Pre R R2 T b L lo hi pS nS) (fun _ => goClass P) (Post R R2 T b L lo hi pS nS) (Panics R R2 T b L lo hi pS nS) :=
  (Fv256.Arm64.MustFromDecimalMain.correctness_proof P impl R R2 T b L lo hi pS nS hI hif hnew hmg hmv hwb1 hwb2 hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi pS nS s s').1 hq)
    (fun s v s2 _ hq => (pan_iff R R2 T b L lo hi pS nS s v s2).1 hq)

namespace Witness

/-- non-vacuity: stub runtime contracts, a 48-digit decimal string, a call state with `PreFd` (incl. `DataLoaded` of the real data and `PanicInit`) -/
theorem nonvacuous : ∃ (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (P : Janus.Spec.PanicRuntime) (ret : Nat) (s : State),
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
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [pS, nS] s ∧
    (Fv256.Arm64.MFdWit.pinPanicRuntime P ∧ Pre R R2 T b L lo hi pS nS s) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    GoReturns ((Extracted.program.link impl).withExit ret) (goClass P) s fun o =>
      match o with
      | .returned s' => ABIReturn s s' ∧ Post R R2 T b L lo hi pS nS s s'
      | .panicked v s' => Panics R R2 T b L lo hi pS nS s v s'
      | .goexited _ => False := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, P, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, hret⟩ := Fv256.Arm64.MustFromDecimalMain.Wit.nonvacuous
  exact ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, P, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, hret.mono fun o ho => by
    cases o with
    | returned s' => exact ⟨ho.1, (post_iff R R2 T b L lo hi pS nS s s').1 ho.2⟩
    | panicked v s' => exact (pan_iff R R2 T b L lo hi pS nS s v s').1 ho
    | goexited s' => exact ho⟩

end Witness

end Fv256.Arm64.MustFromDecimal
