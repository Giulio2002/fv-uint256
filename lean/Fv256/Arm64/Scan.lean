import Extracted
import Fv256.Spec.Scan
import Fv256.Spec.Arm64.ScanSpec
import Fv256.Spec.I
import Fv256.Proofs.Common.SfdBridge
import Fv256.Proofs.Common.ScanBridge
import Fv256.Spec.Arm64.CallSites.Base
import Fv256.Spec.Arm64.SfdTopSpec
import Fv256.Spec.Arm64.Scan
import Fv256.Spec.Arm64.ScanSciSpec
import Fv256.Spec.Arm64.ScanSciBase
import Fv256.Spec.Arm64.SfdCfgE
import Fv256.Proofs.Arm64.Scan

/-!
# arm64: the compiled `(*uint256.Int).Scan` implements `Spec.scan`  (`Fv256/Spec/Scan.lean`)

`dst.Scan(src)` (`X0`, `X1`, `X2` = `dst`, the interface value `src` as type word `tw` and data word `dw`) returns normally (never faults or
panics). What it does is exactly `Fv256.Spec.scan`: `src == nil` gives `0`; a `string` or `[]byte` is parsed as a decimal with optional
`e` exponent (`Spec.scanText`); any other type gives the `"unsupported type"` error. The hypotheses assume the runtime helpers behave as
their contracts. The proof is `Fv256/Proofs/Arm64/Scan.lean`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C

open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSpec Fv256.Arm64.ScanSci

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Scan

/-- PRECONDITION (machine facts only): the standard runtime model, the stack window, the static objects, and for each kind of `src` (nil, string, byte slice, other type) its descriptor and data layout facts; the static data is loaded. -/
def Pre (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (s : State) : Prop :=
  ScanPre cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65» sbAddr stAddr
          Extracted.dataAddr.«type:errors.errorString#8e8100b7» R R2 T b L lo hi dst tw dw s ∧ Extracted.program.DataLoaded s.mem

/-- The result of scanning the text of the string `(p, n)` (read in `s`): it is `Fv256.Spec.scan` of its bytes.
`ok v`: `err = nil` and `*dst = v`; `eof` / `range`: the package errors; `badSyntax`: a `*strconv.NumError` for the chunk `s[lo', lo' + len')`. -/
def StrPost (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (W : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64) (s s' : State) : Prop :=
  match Fv256.Spec.scan (.text (Janus.Spec.strBytes s.mem p.toNat n.toNat)) with
  | .ok v => s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = v ∧ MemFrame s.mem s'.mem (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])
  | .eof => (s'.regs 0).toNat = s.mem.readLE cfg.ioEOF 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.ioEOF + 8) 8 ∧ MemFrame s.mem s'.mem (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])
  | .range => (s'.regs 0).toNat = s.mem.readLE cfg.errBig 8 ∧ (s'.regs 1).toNat = s.mem.readLE (cfg.errBig + 8) 8 ∧ MemFrame s.mem s'.mem (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])
  | .badSyntax lo' len' => ∃ (q : Nat) (t : BitVec 64), s'.regs 0 = BitVec.ofNat 64 cfg.numErrItab ∧ s'.regs 1 = t ∧ SynObj cfg R L (BitVec.ofNat 64 cfg.fnStr) 9#64 (BitVec.ofNat 64 (p.toNat + lo')) (BitVec.ofNat 64 len') s s' q t.toNat ∧ MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)])
  | .unsupported => False

/-- POSTCONDITION: the callee-saved state is kept and, by the kind of `src` (`tw` is the type word: `0` nil, the `string` or `[]uint8`
descriptor, or another type), the outcome is the one `Fv256.Spec.scan` gives; memory changes are confined to the runtime heap, the stack
window and `dst`. -/
def Post (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (s s' : State) : Prop :=
  Kept s s' ∧
  ((tw = 0 ∧ (match Fv256.Spec.scan .nil with
      | .ok v => s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ Janus.Spec.val256 s'.mem dst.toNat = v ∧ MemFrame s.mem s'.mem [(lo, hi), (dst.toNat, dst.toNat + 32)]
      | _ => False)) ∨
   (tw.toNat = Extracted.dataAddr.«type:string#f88732b8» ∧ StrPost R R2 L [] lo hi dst (hdrP s dw) (hdrN s dw) s s') ∨
   (tw.toNat = Extracted.dataAddr.«type:[]uint8#7efbbf65» ∧ StrPost R R2 L R.rt lo hi dst (hdrP s dw) (hdrN s dw) s s') ∨
   (tw ≠ 0 ∧ tw.toNat ≠ Extracted.dataAddr.«type:string#f88732b8» ∧ tw.toNat ≠ Extracted.dataAddr.«type:[]uint8#7efbbf65» ∧ (match Fv256.Spec.scan .other with
      | .unsupported => s'.regs 0 = BitVec.ofNat 64 Extracted.dataAddr.«go:itab.*errors.errorString,error» ∧ (∃ (blk ptr : Nat), s'.regs 1 = BitVec.ofNat 64 blk ∧ InRanges blk 16 R.rt ∧ ApartAll blk 16 L ∧
        s'.mem.readLE blk 8 = ptr ∧ s'.mem.readLE (blk + 8) 8 = 16 ∧ (∀ k, k < 16 → s'.mem.readLE (ptr + k) 1 = unsupB k)) ∧ Janus.Spec.val256 s'.mem dst.toNat = Janus.Spec.val256 s.mem dst.toNat ∧ MemFrame s.mem s'.mem (R.rt ++ [(lo, hi)])
      | _ => False)))

/-- BRIDGE: the string part of the implementation-shaped postcondition is equivalent to `StrPost` (`Fv256.ScanBridge.sciParse_eq`). -/
theorem strPost_iff (R : RtInv) (R2 : IfaceModel) (L : List (Nat × Nat)) (W : List (Nat × Nat)) (lo hi : Nat) (dst p n : BitVec 64) (s s' : State) :
    Fv256.Arm64.ScanSpec.ScanStrPost cfg R R2 L W lo hi dst p n s s' ↔ StrPost R R2 L W lo hi dst p n s s' := by
  unfold Fv256.Arm64.ScanSpec.ScanStrPost StrPost
  rw [Fv256.ScanBridge.sciParse_eq, Fv256.SfdBridge.bl_bytesAt]
  exact Fv256.ScanBridge.sci_match_iff _ _ _ _ _

/-- BRIDGE (not part of the claim): the implementation-shaped postcondition `ScanPost` is equivalent to `Post`. -/
theorem post_iff (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (s s' : State) : (ScanPost cfg Extracted.dataAddr.«type:string#f88732b8» Extracted.dataAddr.«type:[]uint8#7efbbf65»
          Extracted.dataAddr.«go:itab.*errors.errorString,error» R R2 b L lo hi dst tw dw s s') ↔ Post R R2 T b L lo hi dst tw dw s s' := by
  unfold Post Fv256.Arm64.ScanSpec.ScanPost
  simp only [strPost_iff]
  apply and_congr_right
  intro _
  simp only [Fv256.Spec.scan]

/-- THE CLAIM: for every runtime obeying the contracts and every call meeting `Pre`, the compiled code returns (ABI obeyed) in a state meeting `Post`. -/
theorem correctness (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (dst tw dw : BitVec 64)
    (hI : ImplApart Extracted.program impl)
    (hif : Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (hsb : RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive)
    (hcmp : Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16) :
    Ensures (Extracted.program.link impl) Extracted.entry [dst, tw, dw]
      (Pre R R2 T b L lo hi dst tw dw) (Post R R2 T b L lo hi dst tw dw) :=
  (correctness_proof impl R R2 T b L lo hi dst tw dw hI hif hnew hmg hmv hwb1 hwb2 hsb hcmp).mono (fun _ hs => hs) (fun s s' _ hq => (post_iff R R2 T b L lo hi dst tw dw s s').1 hq)

namespace Witness

/-- NON-VACUITY (one kind of `src`; see the proof): the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    Pre R R2 T b L lo hi dst tw dw s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi dst tw dw s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.Scan.Witness.nonvacuous_proof
  exact ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi dst tw dw s s').1 hq⟩⟩

end Witness

namespace NoE.Witness

/-- NON-VACUITY (one kind of `src`; see the proof): the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    Pre R R2 T b L lo hi dst tw dw s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi dst tw dw s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.Scan.NoE.Witness.nonvacuous_proof
  exact ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi dst tw dw s s').1 hq⟩⟩

end NoE.Witness

namespace Nil.Witness

/-- NON-VACUITY (one kind of `src`; see the proof): the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    Pre R R2 T b L lo hi dst tw dw s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi dst tw dw s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.Scan.Nil.Witness.nonvacuous_proof
  exact ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi dst tw dw s s').1 hq⟩⟩

end Nil.Witness

namespace Byt.Witness

/-- NON-VACUITY (one kind of `src`; see the proof): the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    Pre R R2 T b L lo hi dst tw dw s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi dst tw dw s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.Scan.Byt.Witness.nonvacuous_proof
  exact ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi dst tw dw s s').1 hq⟩⟩

end Byt.Witness

namespace Other.Witness

/-- NON-VACUITY (one kind of `src`; see the proof): the hypotheses and `Pre` are jointly satisfiable by a concrete call, which returns with `Post`. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (dst tw dw : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    RtLiveContract (Extracted.program.ofImpl impl) sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [dst, tw, dw] s ∧
    Pre R R2 T b L lo hi dst tw dw s ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 L b s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 sbAddr ∧ RtLivePre 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ Post R R2 T b L lo hi dst tw dw s s' := by
  obtain ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, hret⟩ := Fv256.Arm64.Scan.Other.Witness.nonvacuous_proof
  exact ⟨impl, R, R2, T, b, L, lo, hi, dst, tw, dw, ret, s, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, ⟨c12, c13⟩, c14, c15, c16, c17, c18, c19, c20, hret.1, hret.2.mono fun s' ⟨ha, hq⟩ => ⟨ha, (post_iff R R2 T b L lo hi dst tw dw s s').1 hq⟩⟩

end Other.Witness

end Fv256.Arm64.Scan
