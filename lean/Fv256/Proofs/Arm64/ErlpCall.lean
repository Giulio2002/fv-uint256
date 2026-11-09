import Fv256.Proofs.Arm64.ErlpDefs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the common tail of the two paths with an allocation: the call `w.Write(p)` at `EncodeRLP+0x12c` and the return -/
theorem erlp_call (impl : List Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hw : ICallContract (Extracted.program.link impl) fn 4 stack 96 rt (fun _ => []) R (WP z w))
    (s S2 : State) (h4104 : 4104 ≤ stack) (hfn4 : fn % 4 = 0) (hfn : fn < 2 ^ 56)
    (hwb : 64 + stack ≤ s.sp.toNat) (hwn : s.sp.toNat + 32 ≤ 2 ^ 48)
    (hout : Outside (s.sp.toNat - 64 - stack) (stack + 96) rt)
    (hzo : Outside z.toNat 32 rt)
    (hzd : z.toNat + 32 ≤ s.sp.toNat - 64 - stack ∨ s.sp.toNat - 64 - stack + (stack + 96) ≤ z.toNat)
    (hpc : S2.pc = BitVec.ofNat 64 (Extracted.entry + 0x12c))
    (hr0 : S2.regs 0 = w) (hr5 : S2.regs 5 = BitVec.ofNat 64 fn) (p n : Nat)
    (hr1 : S2.regs 1 = BitVec.ofNat 64 p) (hr2 : S2.regs 2 = BitVec.ofNat 64 n) (hr3 : S2.regs 3 = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hp : p < 2 ^ 64)
    (hsp : S2.sp = s.sp - 64#64) (h29 : S2.regs 29 = s.sp - 72#64) (h28 : S2.regs 28 = s.regs 28)
    (h18 : S2.regs 18 = s.regs 18)
    (hm72 : S2.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat) (hm64 : S2.mem.readLE (s.sp.toNat - 64) 8 = ret)
    (hal : s.sp.toNat % 16 = 0) (hbd : p + n ≤ 2 ^ 48) (hpacc : s.mem.accessible p n false = true)
    (hwa : S2.mem.accessible (s.sp.toNat - (64 + stack)) (64 + stack + 32) true = true)
    (hlen : (rlpBytes (rlpVal S2.mem z.toNat)).length = n)
    (hstr : Janus.Spec.strBytes S2.mem p n = rlpBytes (rlpVal S2.mem z.toNat))
    (hF1 : MemFrame s.mem S2.mem (rt ++ [(s.sp.toNat - 64 - 4096, s.sp.toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S2
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  janus_run [hlen, hstr, hbd, hpacc, hm72, hm64, hwa] calls [hw]
  apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
  · apply epost_ex
    · assumption
    · rfl
    · rfl
  · janus_frame

end Fv256.Arm64.EncodeRLP
