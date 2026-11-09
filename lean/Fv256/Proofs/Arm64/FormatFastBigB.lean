import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Common.IntoBigCommon
import Fv256.Proofs.Common.GrabRetA64

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.IntoBig Fv256.GrabRetA64

namespace Fv256.Arm64.FormatFast

abbrev fmtAddr : Nat := Extracted.program.contractAddr "math/big.(*Int).Format"

/-- the big path, part B: `ldr x0,[sp+48]` ... the static call `math/big.(*Int).Format(b, s, ch)` from `Format+0x214`, epilogue, return -/
theorem big_b (impl : List Segment) (rtF : List (Nat × Nat)) (stack : Nat) (RBf : Res)
    (tab data : BitVec 64) (ch32 P v : Nat) (S0 S1 : State)
    (hBf : ICallContract (Extracted.program.link impl) fmtAddr 4 stack 120 rtF (fun _ => []) RBf
      (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ BigObj sc.mem P v ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch32))
    (hlt : ch32 < 2 ^ 32) (hBO : BigObj S1.mem P v)
    (hpc : S1.pc = BitVec.ofNat 64 (Extracted.entry + 0x214))
    (hsp : S1.sp = S0.sp) (hal : S0.sp.toNat % 16 = 0) (hst : 8 ≤ stack) (hwb : 8 + stack ≤ S0.sp.toNat)
    (hwn : S0.sp.toNat + 0x78 ≤ 2 ^ 48)
    (hwa : S1.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true)
    (hout : Outside (S0.sp.toNat - 8) 128 rtF)
    (hs48 : S1.mem.readLE (S0.sp.toNat + 48) 8 = P) (hP : P < 2 ^ 64)
    (hs96 : S1.mem.readLE (S0.sp.toNat + 96) 8 = tab.toNat) (hs104 : S1.mem.readLE (S0.sp.toNat + 104) 8 = data.toNat)
    (hs112 : S1.mem.readLE (S0.sp.toNat + 112) 4 = ch32)
    (hr0 : S1.mem.readLE S0.sp.toNat 8 = S0.mem.readLE S0.sp.toNat 8)
    (hr8 : S1.mem.readLE (S0.sp.toNat - 8) 8 = S0.mem.readLE (S0.sp.toNat - 8) 8)
    (hret : CodePtrOK (S0.mem.readLE S0.sp.toNat 8)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE S0.sp.toNat 8)) S1
      (fun S' => S'.sp = S0.sp + 80#64 ∧ S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8) ∧
        S'.regs 28 = S1.regs 28 ∧ S'.regs 18 = S1.regs 18 ∧
        MemFrame S1.mem S'.mem (rtF ++ [(S0.sp.toNat - stack, S0.sp.toNat - 8), (S0.sp.toNat + 8, S0.sp.toNat + 8 + 32)]) ∧
        (∃ j0 j1 j2, RBf (BitVec.ofNat 64 P) tab data (BitVec.ofNat 64 (if ch32 < 2 ^ 31 then ch32 else ch32 + 18446744069414584320)) j0 j1 j2)) := by
  simp only [CodePtrOK] at hret
  have hout8 : Outside (S0.sp.toNat - 8) 128 rtF := hout
  have hmodP : P % 2 ^ 64 = P := Nat.mod_eq_of_lt hP
  have hmodC : ch32 % 4294967296 = ch32 := Nat.mod_eq_of_lt hlt
  have hch : (if ch32 < 2147483648 then ch32 else (ch32 + 18446744069414584320) % 4294967296) = ch32 := by
    split <;> omega
  have hEx : ∃ P_1, P = P_1 ∧ BigObj S1.mem P_1 v := ⟨P, rfl, hBO⟩
  janus_run [hEx, hch, hmodP, hmodC, hBO, hsp, hs48, hs96, hs104, hs112, hwa, hr0, hr8] calls [hBf]
  fv_ret_names_a64 junk f v' m ex ep hk1 hpr hfr hR
  exact ⟨hfr, _, _, _, hR⟩

end Fv256.Arm64.FormatFast
