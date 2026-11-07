import Fv256.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
/-- the common tail of the two paths with an allocation: the call `w.Write(p)` at `EncodeRLP+0x14c` and the return -/
theorem erlp_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R (WP z w))
    (s S2 : State) (h4104 : 4104 ≤ stack) (hfn : fn < 2 ^ 47)
    (hwb : 56 + stack ≤ (s.regs 4).toNat) (hwn : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hout : Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hpc : S2.rip = BitVec.ofNat 64 (Extracted.entry + 0x14c))
    (hr0 : S2.regs 0 = w) (hr2 : S2.regs 2 = BitVec.ofNat 64 fn) (p n : Nat)
    (hr3 : S2.regs 3 = BitVec.ofNat 64 p) (hr1 : S2.regs 1 = BitVec.ofNat 64 n) (hr7 : S2.regs 7 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hp : p < 2 ^ 64)
    (hr4 : S2.regs 4 = s.regs 4 - 48#64) (hr5 : S2.regs 5 = s.regs 4 - 8#64) (hr14 : S2.regs 14 = s.regs 14)
    (hx15 : S2.xmm 15 = s.xmm 15) (hdf : S2.df = s.df)
    (hm8 : S2.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) (hmr : S2.mem.readLE (s.regs 4).toNat 8 = ret)
    (hwa : S2.mem.accessible ((s.regs 4).toNat - (56 + stack)) (56 + stack + 32) true = true)
    (hal : (s.regs 4).toNat % 8 = 0) (hbd : p + n ≤ 2 ^ 48) (hpacc : s.mem.accessible p n false = true)
    (hlen : ∀ v, (rlpBytes (rlpVal (S2.mem.writeLE ((s.regs 4).toNat - 56) 8 v) z.toNat)).length = n)
    (hstr : ∀ v, Janus.Spec.strBytes (S2.mem.writeLE ((s.regs 4).toNat - 56) 8 v) p n =
      rlpBytes (rlpVal (S2.mem.writeLE ((s.regs 4).toNat - 56) 8 v) z.toNat))
    (hF1 : MemFrame s.mem S2.mem (rt ++ [((s.regs 4).toNat - 56 - 4096, (s.regs 4).toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S2
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  janus64_run [hlen, hstr, hbd, hpacc, hm8, hmr, hwa] calls [hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Amd64.EncodeRLP
