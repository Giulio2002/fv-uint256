import Extracted
import Fv256.Spec.FromDecimal
import Fv256.Spec.Arm64.FromDecimal
import Fv256.Spec.I
import Fv256.Proofs.Common.SfdBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Proofs.Arm64.FromDecimalMain

/-!
# arm64: the compiled `uint256.FromDecimal` implements `Spec.fromDecimal`  (`Fv256/Spec/FromDecimal.lean`)

`FromDecimal(s)` (`X0`, `X1` = `s.ptr`, `s.len`) returns normally (never faults or panics). Its outcome is exactly `Fv256.Spec.fromDecimal`
of the bytes of `s` (see `Fv256/Spec/SetFromDecimal.lean` for the syntax): for a valid decimal string it returns `(z, nil)` where `z`
is a fresh 32-byte `Int` in the runtime's heap holding the number; otherwise `(nil, err)` with `err` one of `io.EOF`, `ErrBig256Range`
or a `*strconv.NumError` (syntax error). The hypotheses `hif ... hcmp` assume the runtime helpers behave as their contracts.
The proof is `Fv256/Proofs/Arm64/FromDecimalMain.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.EqHashModel Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.CallSites

open Fv256.Arm64.FromDecimal

namespace Fv256.Arm64.FromDecimal

/-- PRECONDITION (machine facts only): the standard runtime model (`R`: allocator, `R2`: interface model), the stack window `[lo, hi)`, the static objects (`io.EOF`, `ErrBig256Range`, the multiplier table, the 78-digit bound string), the string `s` readable and outside the window, and the chunk-copy facts for the error path; the static data is loaded. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s : State) : Prop :=
  Fv256.Arm64.FromDecimal.PreFd R R2 T b L lo hi pS nS s

/-- POSTCONDITION: for `Spec.fromDecimal = ok v`: the first result is a pointer into the runtime heap to a 32-byte block holding `v`, with `err = nil`; for `eof` / `range`: the pointer is `nil` and `err` is `io.EOF` / `ErrBig256Range`; for `badSyntax`: the pointer is `nil` and `err` is a `*strconv.NumError`; only the heap and the window were written. -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s s' : State) : Prop :=
  (match Fv256.Spec.fromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) with
   | .ok v =>
      ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0
   | .eof =>
      s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.ioEOF + 8) 8
   | .range =>
      s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.errBig + 8) 8
   | .badSyntax _ _ =>
      s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 cfg.numErrItab) ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition (`decParse`) is equivalent to `Post`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (s s' : State) :
    ((∀ v, decParse (bytesAt s.mem pS.toNat) nS.toNat = .ok v →
              ∃ ptr : Nat, (s'.regs 0).toNat = ptr ∧ InRanges ptr 32 R.rt ∧ val256 s'.mem ptr = v ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0) ∧
            (decParse (bytesAt s.mem pS.toNat) nS.toNat = .eof →
              s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.ioEOF + 8) 8) ∧
            (decParse (bytesAt s.mem pS.toNat) nS.toNat = .range →
              s'.regs 0 = 0 ∧ (s'.regs 1).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 2).toNat = s.mem.readLE (cfg.errBig + 8) 8) ∧
            (∀ lo' len', decParse (bytesAt s.mem pS.toNat) nS.toNat = .syntax lo' len' →
              s'.regs 0 = 0 ∧ s'.regs 1 = BitVec.ofNat 64 cfg.numErrItab) ∧
            MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi)])) ↔ Post R R2 T b L lo hi pS nS s s' := by
  unfold Post Fv256.Spec.fromDecimal
  rw [Fv256.SfdBridge.decParse_eq, Fv256.SfdBridge.bl_bytesAt]
  generalize Fv256.Spec.setFromDecimal (Janus.Spec.strBytes s.mem pS.toNat nS.toNat) = r
  rw [← and_assoc, ← and_assoc, ← and_assoc]
  apply and_congr_left
  intro _
  rcases r with w | ⟨⟩ | ⟨⟩ | ⟨a, c⟩ <;> simp [Fv256.SfdBridge.toRes, Fv256.I.Res.ok, Fv256.I.Res.eof, Fv256.I.Res.range, Fv256.I.Res.syntax] <;>
    exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ => h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
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
    Ensures (Extracted.program.link impl) Extracted.entry [pS, nS]
      (Pre R R2 T b L lo hi pS nS) (Post R R2 T b L lo hi pS nS) :=
  (Fv256.Arm64.FromDecimalMain.correctness_proof impl R R2 T b L lo hi pS nS hI hif hnew hmg hmv hwb1 hwb2 hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi pS nS s s').1 hq)

namespace Witness

/-- non-vacuity: a concrete runtime (stub contracts), a 48-digit decimal string, and a call state with `PreFd`, `DataLoaded` of the real data -/
theorem nonvacuous : ∃ (impl : List Janus.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (pS nS : BitVec 64) (ret : Nat) (s : State),
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
    Pre R R2 T b L lo hi pS nS s ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi pS nS s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, hret⟩ := Fv256.Arm64.FromDecimalMain.Wit.nonvacuous
  exact ⟨impl, R, R2, T, b, L, lo, hi, pS, nS, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, hret.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi pS nS s s').1 hq⟩⟩

end Witness

end Fv256.Arm64.FromDecimal
