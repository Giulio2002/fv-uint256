import Fv256.Arm64.ErlpDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `1 ≤ bitlen ≤ 7`, second half: from the return of `newobject([1]byte)` (`EncodeRLP+0x150`) to the return -/
theorem erlp_p1b (impl : List Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hw : ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R (WP z w))
    (s S1 : State) (h4104 : 4104 ≤ stack) (hfn4 : fn % 4 = 0) (hfn : fn < 2 ^ 56)
    (hwb : 64 + stack ≤ s.sp.toNat) (hwn : s.sp.toNat + 32 ≤ 2 ^ 48)
    (hout : Outside (s.sp.toNat - 64 - stack) (stack + 96) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt)
    (hal : s.sp.toNat % 16 = 0)
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (v : Nat) (hv7 : v < 128) (hrb : rlpBytes v = [v])
    (hpc : S1.pc = BitVec.ofNat 64 (Extracted.entry + 0x150)) (obj : Nat) (hr0 : S1.regs 0 = BitVec.ofNat 64 obj)
    (hin : InRanges obj 1 rt) (hob : obj + 1 ≤ 2 ^ 48) (hoacc : S1.mem.accessible obj 1 true = true)
    (hdj : s.sp.toNat - 64 - stack + (stack + 96) ≤ obj ∨ obj + 1 ≤ s.sp.toNat - 64 - stack)
    (hdz : z.toNat + 32 ≤ obj ∨ obj + 1 ≤ z.toNat) (hdt : tab.toNat + 24 + 8 ≤ obj ∨ obj + 1 ≤ tab.toNat + 24)
    (hsp : S1.sp = s.sp - 64#64) (h29 : S1.regs 29 = s.sp - 72#64) (h28 : S1.regs 28 = s.regs 28)
    (h18 : S1.regs 18 = s.regs 18)
    (hm72 : S1.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat) (hm64 : S1.mem.readLE (s.sp.toNat - 64) 8 = ret)
    (hmz : S1.mem.readLE (s.sp.toNat + 8) 8 = z.toNat)
    (hm16 : S1.mem.readLE (s.sp.toNat + 16) 8 = tab.toNat) (hm24 : S1.mem.readLE (s.sp.toNat + 24) 8 = w.toNat)
    (hz8 : S1.mem.readLE z.toNat 8 = v) (hz32 : S1.mem.readLE z.toNat 32 = v)
    (hzacc : S1.mem.accessible z.toNat 8 false = true)
    (hfn' : S1.mem.readLE (tab.toNat + 24) 8 = fn) (hta : S1.mem.accessible (tab.toNat + 24) 8 false = true)
    (hwa : S1.mem.accessible (s.sp.toNat - (64 + stack)) (64 + stack + 32) true = true)
    (hF1 : MemFrame s.mem S1.mem (rt ++ [(s.sp.toNat - 64 - 4096, s.sp.toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S1
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  have hmod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
  janus_run [hfn', rlpVal, hz8, hz32, hzacc, hrb, hmod, hzn, strBytes_write1, List.length_singleton, hm72, hm64, hmz,
    hm16, hm24, hta, hwa] calls [hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Arm64.EncodeRLP
