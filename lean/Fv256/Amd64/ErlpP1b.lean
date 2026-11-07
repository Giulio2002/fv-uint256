import Fv256.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the path `1 ≤ bitlen ≤ 7`, second half: from the return of `newobject([1]byte)` (`EncodeRLP+0x166`) to the return -/
theorem erlp_p1b (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R (WP z w))
    (s S1 : State) (h4104 : 4104 ≤ stack) (hfn : fn < 2 ^ 47)
    (hwb : 56 + stack ≤ (s.regs 4).toNat) (hwn : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hout : Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt)
    (hal : (s.regs 4).toNat % 8 = 0)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (v : Nat) (hv7 : v < 128) (hrb : rlpBytes v = [v])
    -- the state after `newobject`
    (hpc : S1.rip = BitVec.ofNat 64 (Extracted.entry + 0x166)) (obj : Nat) (hr0 : S1.regs 0 = BitVec.ofNat 64 obj)
    (hin : InRanges obj 1 rt) (hob : obj + 1 ≤ 2 ^ 48) (hoacc : S1.mem.accessible obj 1 true = true)
    (hdj : (s.regs 4).toNat - 56 - stack + (stack + 88) ≤ obj ∨ obj + 1 ≤ (s.regs 4).toNat - 56 - stack)
    (hdz : z.toNat + 32 ≤ obj ∨ obj + 1 ≤ z.toNat) (hdt : tab.toNat + 24 + 8 ≤ obj ∨ obj + 1 ≤ tab.toNat + 24)
    (hr4 : S1.regs 4 = s.regs 4 - 48#64) (hr5 : S1.regs 5 = s.regs 4 - 8#64) (hr14 : S1.regs 14 = s.regs 14)
    (hx15 : S1.xmm 15 = s.xmm 15) (hdf : S1.df = s.df)
    (hm8 : S1.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) (hmr : S1.mem.readLE (s.regs 4).toNat 8 = ret)
    (hmz : S1.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat)
    (hm16 : S1.mem.readLE ((s.regs 4).toNat + 16) 8 = tab.toNat) (hm24 : S1.mem.readLE ((s.regs 4).toNat + 24) 8 = w.toNat)
    (hz8 : S1.mem.readLE z.toNat 8 = v) (hz32 : S1.mem.readLE z.toNat 32 = v)
    (hzacc : S1.mem.accessible z.toNat 8 false = true)
    (hfn' : S1.mem.readLE (tab.toNat + 24) 8 = fn) (hta : S1.mem.accessible (tab.toNat + 24) 8 false = true)
    (hwa : S1.mem.accessible ((s.regs 4).toNat - (56 + stack)) (56 + stack + 32) true = true)
    (hF1 : MemFrame s.mem S1.mem (rt ++ [((s.regs 4).toNat - 56 - 4096, (s.regs 4).toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S1
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  have hmod : v % 256 = v := Nat.mod_eq_of_lt (by omega)
  have hdata : True := trivial
  janus64_run [rlpVal, hz8, hz32, hzacc, hrb, hmod, hzn, strBytes_write1, List.length_singleton, hm8, hmr, hmz, hm16, hm24,
    hfn', hta, hwa] calls [hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Amd64.EncodeRLP
