import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.GrabRetA64
import Fv256.DecAt
import Fv256.SpecC
import Fv256.SpecE
import Fv256.Arm64.FM.IntoBigDefs
import Fv256.Arm64.FormatFastBigB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.EqHashModel
open Fv256.FormatFastA64 Fv256.E Fv256.IntoBig Fv256.Arm64.IntoBig

namespace Fv256.Arm64.Dec
abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
end Fv256.Arm64.Dec
open Fv256.Arm64.Dec
namespace Fv256.Arm64.FormatFast
abbrev nmHex : String := "github.com/holiman/uint256.(*Int).Hex"
abbrev P0H (impl : List Segment) : Program := (Extracted.program.onlySegments [nmHex]).link impl
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"
theorem fast_arm64 (impl : List Segment) (R2 : RtInv) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (RW RP RF RWr : Res) (z tab data : BitVec 64) (hI : ImplApart Extracted.program impl)
    (hW : ICallContract (Extracted.program.link impl) fW 1 stack 120 rt (fun _ => []) RW (fun _ => True) (RtPreserves R2))
    (hP : ICallContract (Extracted.program.link impl) fP 1 stack 120 rt (fun _ => []) RP (fun _ => True) (RtPreserves R2))
    (hF : ICallContract (Extracted.program.link impl) fF 2 stack 120 rt (fun _ => []) RF (fun _ => True) (RtPreserves R2))
    (S0 : State)
    (hWr : ICallContract (Extracted.program.link impl) fWr 4 stack 120 rt (fun _ => []) RWr
      (FastWP data (Fv256.FormatSpec.fastBytes (val256 S0.mem z.toNat) ((S0.regs 3).toNat % 2 ^ 32))))
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hcH : RtContract (P0H impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (hrt32 : ∀ r ∈ rt, 32 ≤ r.1)
    (hpc : S0.pc = BitVec.ofNat 64 (Extracted.entry + 0x44))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0)
    (hwR : Outside (S0.sp.toNat - stack) (stack + 0x78) R2.rt)
    (h4608 : 4608 ≤ stack)
    (hdl : Extracted.program.DataLoaded S0.mem) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (ht1 : Outside 989280 256 rt) (ht2 : Outside 1002589 256 rt) (ht3 : Outside 968614 256 rt)
    (hg : GuardOK S0 688) (hgo : Outside ((S0.regs 28).toNat + 16) 8 rt)
    (hgd : (S0.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S0.regs 28).toNat + 16)
    (hH1 : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → 2 ^ 64 ≤ val256 S0.mem z.toNat →
      H [0, S0.sp.toNat - 384 + 94 + (98 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384) (rtView rt M))
    (hH2 : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → 100 ≤ val256 S0.mem z.toNat →
      val256 S0.mem z.toNat < 2 ^ 64 →
      H [0, S0.sp.toNat - 384 - 32 + (24 - decLen (val256 S0.mem z.toNat)), decLen (val256 S0.mem z.toNat)]
        (S0.regs 28).toNat (S0.sp.toNat - 384 - 96) (rtView rt M))
    (hHst : ∀ M p l, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → StrOut M p l (decBytes (val256 S0.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l → H [0, p, l] (S0.regs 28).toNat S0.sp.toNat (rtView rt M))
    (hHx : ∀ M, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → ∀ n, Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      H [0, S0.sp.toNat - 112 + 38 + (64 - n), n + 2] (S0.regs 28).toNat (S0.sp.toNat - 112) (rtView rt M))
    (hHstx : ∀ M p l n, MemFrame S0.mem M (FL rt S0.sp.toNat stack) → Fv256.C.hexDigits (val256 S0.mem z.toNat) n →
      StrOut M p l (Fv256.C.hexStrBytes (val256 S0.mem z.toNat) n) → InRanges p l rt →
      H [0, p + 2, l - 2] (S0.regs 28).toNat S0.sp.toNat (rtView rt M))
    (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    RT (Extracted.program.link impl) S0
      [(S0.mem.readLE S0.sp.toNat 8, fun S' =>
          ((S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
            S'.regs 28 = S0.regs 28 ∧ S'.regs 18 = S0.regs 18 ∧
            MemFrame S0.mem S'.mem (FL rt S0.sp.toNat stack) ∧
            (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2)) ∧
          (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
          ((S0.regs 3).toNat % 2 ^ 32 = 100 ∨ (S0.regs 3).toNat % 2 ^ 32 = 115 ∨ (S0.regs 3).toNat % 2 ^ 32 = 118 ∨
            (S0.regs 3).toNat % 2 ^ 32 = 120)) ∧ S'.mem.regions = S0.mem.regions),
       (Extracted.entry + 0x204, fun S' => (FInv rt stack z tab data ((S0.regs 3).toNat % 2 ^ 32) S0 S' ∧ RPres R2 S0 S' ∧
          NotPlain RW RP RF data fW fP fF (S0.regs 3) ((S0.regs 3).toNat % 2 ^ 32)) ∧ S'.mem.regions = S0.mem.regions)] := sorry

theorem big_path (impl : List Segment) (hI : ImplApart Extracted.program impl) (R : RtInv) (b0 : Nat)
    (hnew : NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hwb1 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2)
    (rt rtF : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RBf : Res) (z tab data : BitVec 64) (ch32 : Nat)
    (S0 S : State)
    (hBf : ICallContract (Extracted.program.link impl) fmtAddr 4 stack 120 rtF (fun _ => []) RBf
      (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ BigObj sc.mem P (val256 S0.mem z.toNat) ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch32))
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x204))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (hlt : ch32 < 2 ^ 32) (h4608 : 4608 ≤ stack) (hz0 : z.toNat ≠ 0)
    (hdl : Extracted.program.DataLoaded S.mem) (hg : GuardOK S 4144)
    (hgd : (S.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S.regs 28).toNat + 16)
    (hgr : Outside ((S.regs 28).toNat + 16) 8 R.rt)
    (hfl : S.mem.accessible flagAddr 4 false = true) (ht1 : Outside bigType 16 R.rt) (ht2 : Outside arrType 16 R.rt)
    (hok1 : R.ok (Extracted.program.contractAddr "runtime.newobject") [bigType])
    (hok2 : R.ok (Extracted.program.contractAddr "runtime.newobject") [arrType])
    (hok3 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1])
    (hok4 : R.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2])
    (hinv : R.inv b0 [] (S.regs 28).toNat (view R.rt [] S.mem)) (hbud : blockSize 32 false + blockSize 32 true ≤ b0)
    (hRout : Outside (S0.sp.toNat - stack) (stack + 0x78) R.rt) (hzR : Outside z.toNat 32 R.rt)
    (hoF : Outside (S0.sp.toNat - 8) 128 rtF) (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S
      (fun S' => S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
        S'.regs 28 = S.regs 28 ∧ S'.regs 18 = S.regs 18 ∧
        MemFrame S.mem S'.mem (R.rt ++ rtF ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 56)]) ∧
        (∃ P j0 j1 j2, RBf (BitVec.ofNat 64 P) tab data
          (BitVec.ofNat 64 (if ch32 < 2 ^ 31 then ch32 else ch32 + 18446744069414584320)) j0 j1 j2)) := sorry

end Fv256.Arm64.FormatFast
