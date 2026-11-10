import Extracted
import Fv256.Spec.UnmarshalJSON
import Fv256.Spec.I
import Fv256.Spec.C
import Fv256.Proofs.Common.SfdBridge
import Fv256.Proofs.Common.HexBridge
import Fv256.Proofs.Common.UnmarshalBridge
import Fv256.Spec.Amd64.SfdTopSpec
import Fv256.Spec.Amd64.UnmarshalTextS0
import Fv256.Spec.Amd64.UnmarshalSpec
import Fv256.Spec.Amd64.UnmarshalHex
import Fv256.Spec.Amd64.FromHexLib
import Fv256.Spec.Amd64.UnmarshalQ
import Fv256.Spec.Amd64.UnmarshalJSON0
import Fv256.Spec.Amd64.CallSites.Live
import Fv256.Proofs.Amd64.UnmarshalJSONMain

/-!
# amd64: the compiled `(*uint256.Int).UnmarshalJSON` implements `Spec.unmarshalJSON`  (`Fv256/Spec/UnmarshalJSON.lean`)

`z.UnmarshalJSON(input)` (`RAX`, `RBX`, `RCX` = `z`, `input.ptr`, `input.len`, ...) returns normally (never faults or panics) and its outcome is
exactly `Fv256.Spec.unmarshalJSON` of the bytes of `input`: a quoted input is parsed as `UnmarshalText` of the text between the quotes,
anything else as a decimal number. On success `z` holds the number and `err = nil`. Only `z[0, 32)` and the runtime heap are written.
The hypotheses assume the runtime helpers behave as their contracts.
The proof is `Fv256/Proofs/Amd64/UnmarshalJSONMain.lean`.
-/

open Fv256.Amd64.UnmarshalQ

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.C

open Fv256.Amd64.SfdTopSpec Fv256.Amd64.UnmarshalSpec Fv256.Amd64.UnmarshalHex Fv256.Amd64.FromHexLib

open Fv256.Amd64.UnmarshalJSON

namespace Fv256.Amd64.UnmarshalJSON

/-- PRECONDITION (machine facts only): the standard runtime model (`R`, `R2`), the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, the multiplier table, the digit and error tables), `z` writable and the input readable, all outside the window, the chunk-copy facts for the decimal error path (for the whole input, or for the text between the quotes when it is quoted), and the allocation facts for copying that text. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s : State) : Prop :=
  ((PreU0m cfg sbAddr stAddr R R2 T b L lo hi z pI nI s ∧ (¬ Quoted s.mem pI.toNat nI.toNat → OkOut sbAddr R pI nI s)) ∧ HexEnv R lo hi z s) ∧ (Quoted s.mem pI.toNat nI.toNat → QPre cfg sbAddr R b lo pI nI s)

/-- POSTCONDITION: the outcome is `Spec.unmarshalJSON` of the input bytes (read BEFORE the call), with the same meaning of each result as for `UnmarshalText` (`ok v`: `err = nil`, `*z = v`; `hexError e`: the error variable of `e`; `decEof` / `decRange`: `io.EOF` / `ErrBig256Range`; `decSyntax`: a `*strconv.NumError`); memory changes are confined to the heap and `z`. -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.unmarshalJSON (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) with
   | .ok v =>
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v
   | .hexError e =>
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag) 8) ∧
              s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e.tag + 8) 8)
   | .decEof =>
      (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = 0
   | .decRange =>
      (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
            Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat
   | .decSyntax _ _ =>
      s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab) ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decParse/parseHex`) is equivalent to `Post`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (s s' : State) :
    ((Quoted s.mem pI.toNat nI.toNat →
              (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
                (∀ v, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
                  s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
                (∀ e, parseHex (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .error e →
                  s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
                  s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) ∧
              (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2) →
                (∀ v, decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .ok v →
                s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
              (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .eof →
                (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
                Janus.Spec.val256 s'.mem z.toNat = 0) ∧
              (decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .range →
                (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
                Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
              (∀ lo' len', decParse (bytesAt s.mem (pI.toNat + 1)) (nI.toNat - 2) = .syntax lo' len' →
                s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab))) ∧
            (¬ Quoted s.mem pI.toNat nI.toNat →
              (∀ v, decParse (bytesAt s.mem pI.toNat) nI.toNat = .ok v →
                s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
              (decParse (bytesAt s.mem pI.toNat) nI.toNat = .eof →
                (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧
                Janus.Spec.val256 s'.mem z.toNat = 0) ∧
              (decParse (bytesAt s.mem pI.toNat) nI.toNat = .range →
                (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 3).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧
                Janus.Spec.val256 s'.mem z.toNat = Janus.Spec.val256 s.mem z.toNat) ∧
              (∀ lo' len', decParse (bytesAt s.mem pI.toNat) nI.toNat = .syntax lo' len' →
                s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab)) ∧
            MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])) ↔ Post R R2 T b L lo hi z pI nI cI s s' := by
  unfold Post Fv256.Spec.unmarshalJSON Fv256.Spec.unmarshalText
  simp only [Fv256.HexBridge.parseHex_eq, Fv256.SfdBridge.decParse_eq, Fv256.HexBridge.bl_bytesAt]
  rw [← and_assoc]
  apply and_congr_left
  intro _
  have kq := Fv256.UnmarshalBridge.quoted_iff s.mem pI.toNat nI.toNat
  by_cases hq : Quoted s.mem pI.toNat nI.toNat
  · have e : Fv256.Spec.isQuoted (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = true := kq.2 hq
    have hn : 2 ≤ nI.toNat := hq.1
    have h1 : (¬ Quoted s.mem pI.toNat nI.toNat) = False := eq_false (fun h => h hq)
    simp only [e, ite_true, Fv256.UnmarshalBridge.inner_eq _ _ _ hn, imp_iff_right hq, h1, false_implies, and_true]
    have key := Fv256.UnmarshalBridge.hasHexPrefix_iff s.mem (pI.toNat + 1) (nI.toNat - 2)
    by_cases hh : IsHex s.mem (pI.toNat + 1) (nI.toNat - 2)
    · have e2 : Fv256.Spec.hasHexPrefix (Janus.Spec.strBytes s.mem (pI.toNat + 1) (nI.toNat - 2)) = true := key.2 hh
      have h2 : (¬ IsHex s.mem (pI.toNat + 1) (nI.toNat - 2)) = False := eq_false (fun h => h hh)
      simp only [e2, ite_true, imp_iff_right hh, h2, false_implies, and_true]
      generalize Fv256.Spec.setFromHex (Janus.Spec.strBytes s.mem (pI.toNat + 1) (nI.toNat - 2)) = r
      cases r <;> simp [Fv256.Spec.TextResult.ofHex, Fv256.HexBridge.toExcept]
    · have e2 : ¬ (Fv256.Spec.hasHexPrefix (Janus.Spec.strBytes s.mem (pI.toNat + 1) (nI.toNat - 2)) = true) := fun h => hh (key.1 h)
      have h2 : (IsHex s.mem (pI.toNat + 1) (nI.toNat - 2)) = False := eq_false hh
      simp only [e2, ite_false, h2, false_implies, true_and, imp_iff_right hh]
      generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem (pI.toNat + 1) (nI.toNat - 2)) = r
      rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.Spec.TextResult.ofDec, Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax]
  · have e : ¬ (Fv256.Spec.isQuoted (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = true) := fun h => hq (kq.1 h)
    have h1 : (Quoted s.mem pI.toNat nI.toNat) = False := eq_false hq
    simp only [e, ite_false, h1, false_implies, true_and, imp_iff_right hq]
    generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pI.toNat nI.toNat) = r
    rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.Spec.TextResult.ofDec, Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax]

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pI nI cI : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsb : RtLiveContract64 (Extracted.program.link impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)

    (hcmp : Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [z, pI, nI, cI]
      (Pre R R2 T b L lo hi z pI nI cI) (Post R R2 T b L lo hi z pI nI cI) :=
  (Fv256.Amd64.UnmarshalJSONMain.correctness_proof impl R R2 T b L lo hi z pI nI cI hif hnew hmg hmv hwb1 hwb2 hsb hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi z pI nI cI s s').1 hq)

namespace Witness

/-- NON-VACUITY: the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (z pI nI cI : BitVec 64) (ret : Nat) (s : State),
    Janus.Contracts.IfaceAmd64.Ifaceeq (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract64 (Extracted.program.link impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Janus.Contracts.Cmpstring.CmpstringContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RtLiveContract64 (Extracted.program.link impl) Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R
      (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ Fv256.CallSites.NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ Fv256.CallSites.MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ Fv256.CallSites.MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 Lc bc s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ Fv256.CallSites.WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 Lc bc s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre64 16 s_c) ∧
    (∃ s_c : State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ Fv256.CallSites.IfaceeqSite R2 s_c) ∧
    (∃ (Lc : List (Nat × Nat)) (bc : Nat) (s_c : State), s_c.rip = BitVec.ofNat 64 Fv256.Amd64.UnmarshalTextS.sbAddr ∧
      RtLivePre64 4096 R (slicebytetostringSpec Fv256.Amd64.UnmarshalTextS.stAddr) slicebytetostringLive Fv256.Amd64.UnmarshalTextS.sbAddr Lc bc s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pI, nI, cI] s ∧
    (Pre R R2 T b L lo hi z pI nI cI s) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi z pI nI cI s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, hret⟩ := Fv256.Amd64.UnmarshalJSONMain.Wit.nonvacuous
  exact ⟨impl, R, R2, T, b, L, lo, hi, z, pI, nI, cI, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi z pI nI cI s s').1 hq⟩⟩

end Witness

end Fv256.Amd64.UnmarshalJSON
