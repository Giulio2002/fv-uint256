import Extracted
import Fv256.Spec.UnmarshalText
import Fv256.Spec.I
import Fv256.Spec.C
import Fv256.Proofs.Common.SfdBridge
import Fv256.Proofs.Common.HexBridge
import Fv256.Proofs.Common.UnmarshalBridge
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.UnmarshalTextHead
import Fv256.Spec.Arm64.UnmarshalSpec
import Fv256.Spec.Arm64.UnmarshalHex
import Fv256.Spec.Arm64.UnmarshalPost
import Fv256.Spec.Arm64.UnmarshalJPost
import Fv256.Spec.Arm64.UnmarshalSpecJ
import Fv256.Spec.Arm64.UnmarshalJSONHead
import Fv256.Spec.Arm64.FromHexLib
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.UnmarshalTextMain

/-!
# arm64: the compiled `(*uint256.Int).UnmarshalText` implements `Spec.unmarshalText`  (`Fv256/Spec/UnmarshalText.lean`)

`z.UnmarshalText(input)` (`X0`, `X1`, `X2` = `z`, `input.ptr`, `input.len`, ...) returns normally (never faults or panics) and its outcome is
exactly `Fv256.Spec.unmarshalText` of the bytes of `input`: hexadecimal with a `0x`/`0X` prefix (the six `SetFromHex` errors), decimal
otherwise (`io.EOF`, `ErrBig256Range`, or a `*strconv.NumError`); on success `z` holds the number and `err = nil`. Only `z[0, 32)` and the runtime
heap are written. The hypotheses assume the runtime helpers behave as their contracts.
The proof is `Fv256/Proofs/Arm64/UnmarshalTextMain.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel
  Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalHex Fv256.Arm64.UnmarshalPost Fv256.Arm64.FromHexLib

open Fv256.Arm64.CallSites



namespace Fv256.Arm64.UnmarshalText

/-- PRECONDITION (machine facts only): the standard runtime model (`R`, `R2`), the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, the multiplier table, the digit and error tables), `z` writable and the input readable, all outside the window, and the chunk-copy facts for the decimal error path. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s : State) : Prop :=
  PreU Fv256.Arm64.UnmarshalText.cfg Fv256.Arm64.UnmarshalText.sbAddr Fv256.Arm64.UnmarshalText.stAddr R R2 T b L lo hi
            z pI nI s ∧ HexEnv R lo hi z s

/-- POSTCONDITION: the outcome is `Spec.unmarshalText` of the input bytes (read BEFORE the call): `ok v` gives `err = nil` and `*z = v`; `hexError e` the error variable selected by `e` (via `HexError.tag`); `decEof` / `decRange` the package errors `io.EOF` / `ErrBig256Range` (with `*z` = 0 / unchanged); `decSyntax` a `*strconv.NumError`; memory changes are confined to the heap and `z`. -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.unmarshalText (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) with
   | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v
   | .hexError e =>
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag) 8) ∧
      s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag + 8) 8)
   | .decEof =>
      (s'.regs 0).toNat = s.mem.readLE Fv256.Arm64.UnmarshalText.cfg.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (Fv256.Arm64.UnmarshalText.cfg.ioEOF + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = 0
   | .decRange =>
      (s'.regs 0).toNat = s.mem.readLE Fv256.Arm64.UnmarshalText.cfg.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (Fv256.Arm64.UnmarshalText.cfg.errBig + 8) 8 ∧
      Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat
   | .decSyntax _ _ =>
      s'.regs 0 = BitVec.ofNat 64 Fv256.Arm64.UnmarshalText.cfg.numErrItab) ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`UTPost`) is equivalent to `Post`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s s' : State) :
    (UTPost Fv256.Arm64.UnmarshalText.cfg R R2 lo hi z pI.toNat nI.toNat s s') ↔ Post R R2 T b L lo hi z pI nI cI s s' := by
  unfold Post Fv256.Spec.unmarshalText
  unfold Fv256.Arm64.UnmarshalPost.UTPost Fv256.Arm64.UnmarshalPost.HexPart Fv256.Arm64.UnmarshalPost.DecPart
  simp only [Fv256.HexBridge.parseHex_eq, Fv256.SfdBridge.decParse_eq, Fv256.HexBridge.bl_bytesAt]
  rw [← and_assoc]
  apply and_congr_left
  intro _
  have key := Fv256.UnmarshalBridge.hasHexPrefix_iff s.mem pI.toNat nI.toNat
  by_cases hh : IsHex s.mem pI.toNat nI.toNat
  · have e : Fv256.Spec.hasHexPrefix (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = true := key.2 hh
    have h1 : (¬ IsHex s.mem pI.toNat nI.toNat) = False := eq_false (fun h => h hh)
    simp only [e, ite_true, imp_iff_right hh, h1, false_implies, and_true]
    generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = r
    cases r <;> simp [Fv256.Spec.TextResult.ofHex, Fv256.HexBridge.toExcept]
  · have e : ¬ (Fv256.Spec.hasHexPrefix (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = true) := fun h => hh (key.1 h)
    have h1 : (IsHex s.mem pI.toNat nI.toNat) = False := eq_false hh
    simp only [e, ite_false, h1, false_implies, true_and, imp_iff_right hh]
    generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = r
    rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.Spec.TextResult.ofDec, Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax]

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16)
    (hsb : RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalText.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalText.stAddr) slicebytetostringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (Pre R R2 T b L lo hi z pI nI cI) (Post R R2 T b L lo hi z pI nI cI) :=
  (Fv256.Arm64.UnmarshalTextMain.correctness_proof impl R R2 T b L lo hi z pI nI cI hI hif hnew hmg hmv hwb1 hwb2 hcmp hsb).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi z pI nI cI s s').1 hq)

namespace Witness

/-- Non-vacuity: a concrete runtime (stub code at the contract addresses: allocation, copy, write barriers, interface equality,
string comparison and the live `slicebytetostring` copying a 48-digit input into a fresh block; toy allocator `R`, interface model
`R0`), a stack window and a call `UnmarshalText(z, "777…7")` satisfy EVERY hypothesis of `correctness` (the `ImplApart` premise,
the eight runtime contracts, the call setup) and its precondition (`PreU`, `HexEnv`). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract (Extracted.program.ofImpl impl) Fv256.Arm64.UnmarshalText.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Arm64.UnmarshalText.stAddr) slicebytetostringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    Pre R R2 T b L lo hi z pI nI cI s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 Fv256.Arm64.UnmarshalText.sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec Fv256.Arm64.UnmarshalText.stAddr) slicebytetostringLive Fv256.Arm64.UnmarshalText.sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi z pI nI cI s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.UnmarshalTextMain.Wit.nonvacuous
  exact ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi z pI nI cI s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.UnmarshalText
