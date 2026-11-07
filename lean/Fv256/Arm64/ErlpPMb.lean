import Fv256.Arm64.ErlpDefs
import Fv256.Arm64.ErlpCall
import Fv256.RlpBytes
import Fv256.RlpArm

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Arm64.EncodeRLP

/-- the facts about the object that the `Write` call needs, over the abstract memory `S1.mem` -/
theorem erlp_pmf (s S1 : State) (z : BitVec 64) (obj bl : Nat) (hzn : z.toNat ≠ 0)
    (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl) (hb256 : bl ≤ 256)
    (hzr : S1.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32) (hdz : z.toNat + 32 ≤ obj ∨ obj + 48 ≤ z.toNat) :
    (rlpBytes (rlpVal (armChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)) z.toNat)).length = (bl + 7) / 8 + 1 ∧
    Janus.Spec.strBytes (armChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)) (obj + (32 - (bl + 7) / 8))
        ((bl + 7) / 8 + 1) =
      rlpBytes (rlpVal (armChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)) z.toNat) := by
  refine ⟨?_, ?_⟩
  · rw [arm_rlpVal0 _ _ _ _ _ _ _ _ (by omega) (by omega), rlpVal, if_neg hzn, hzr, rlpBytes_length_multi _ (by omega), hbl]
  · rw [arm_rlpVal0 _ _ _ _ _ _ _ _ (by omega) (by omega), rlpVal, if_neg hzn, hzr, Util.readLE_32]
    exact arm_pmstr S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8) (s.mem.readLE (z.toNat + 16) 8)
      (s.mem.readLE (z.toNat + 24) 8) _ bl (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
      (Util.readLE8_lt _ _) (by rw [← Util.readLE_32]) (by rw [← Util.readLE_32, hbl]) (by omega) hb256

set_option maxRecDepth 100000 in
/-- the path `8 ≤ bitlen`, second half: from the return of `newobject([33]byte)` (`EncodeRLP+0xa8`) to the Write call -/
theorem erlp_pmb (impl : List Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
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
    (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl) (hb256 : bl ≤ 256)
    (hpc : S1.pc = BitVec.ofNat 64 (Extracted.entry + 0xa8)) (obj : Nat) (hreg0 : S1.regs 0 = BitVec.ofNat 64 obj)
    (hin : InRanges obj 48 rt) (hob : obj + 48 ≤ 2 ^ 48) (hoacc : S1.mem.accessible obj 48 true = true)
    (hdj : s.sp.toNat - 64 - stack + (stack + 96) ≤ obj ∨ obj + 48 ≤ s.sp.toNat - 64 - stack)
    (hdz : z.toNat + 32 ≤ obj ∨ obj + 48 ≤ z.toNat) (hdt : tab.toNat + 24 + 8 ≤ obj ∨ obj + 48 ≤ tab.toNat + 24)
    (hsp : S1.sp = s.sp - 64#64) (h29 : S1.regs 29 = s.sp - 72#64) (h28 : S1.regs 28 = s.regs 28)
    (h18 : S1.regs 18 = s.regs 18)
    (hm72 : S1.mem.readLE (s.sp.toNat - 72) 8 = (s.regs 29).toNat) (hm64 : S1.mem.readLE (s.sp.toNat - 64) 8 = ret)
    (hmz : S1.mem.readLE (s.sp.toNat + 8) 8 = z.toNat) (hmbl : S1.mem.readLE (s.sp.toNat - 16) 8 = bl)
    (hm16 : S1.mem.readLE (s.sp.toNat + 16) 8 = tab.toNat) (hm24 : S1.mem.readLE (s.sp.toNat + 24) 8 = w.toNat)
    (hr0 : S1.mem.readLE (z.toNat) 8 = s.mem.readLE (z.toNat) 8) (ha0 : S1.mem.accessible (z.toNat) 8 false = true)
    (hr1 : S1.mem.readLE (z.toNat + 8) 8 = s.mem.readLE (z.toNat + 8) 8) (ha1 : S1.mem.accessible (z.toNat + 8) 8 false = true)
    (hr2 : S1.mem.readLE (z.toNat + 16) 8 = s.mem.readLE (z.toNat + 16) 8) (ha2 : S1.mem.accessible (z.toNat + 16) 8 false = true)
    (hr3 : S1.mem.readLE (z.toNat + 24) 8 = s.mem.readLE (z.toNat + 24) 8) (ha3 : S1.mem.accessible (z.toNat + 24) 8 false = true)
    (hzr : S1.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32)
    (hfn' : S1.mem.readLE (tab.toNat + 24) 8 = fn) (hta : S1.mem.accessible (tab.toNat + 24) 8 false = true)
    (hwa : S1.mem.accessible (s.sp.toNat - (64 + stack)) (64 + stack + 32) true = true)
    (hF1 : MemFrame s.mem S1.mem (rt ++ [(s.sp.toNat - 64 - 4096, s.sp.toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S1
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  have hX := xa_sh bl hb256
  have hn32 : (bl + 7) / 8 ≤ 32 := by omega
  have hd1 := d_bvA _ hn32
  have hd2 := dn_bvA _ hn32
  have he := e_bvA _ hn32
  have hca := ca_eq bl hb8 hb256
  janus_run [hX, hd1, hd2, he, hca, hfn', hzr, hr0, hr1, hr2, hr3, ha0, ha1, ha2, ha3, hzn, hm72, hm64, hmz, hmbl, hm16, hm24, hta, hwa]
    until [Extracted.entry + 0x12c]
  refine erlp_call impl rt fn stack R z tab w ret hret hw s _ h4104 hfn4 hfn hwb hwn hout hzo hzd rfl ?hr0' ?hr5
    (obj + (32 - (bl + 7) / 8)) ((bl + 7) / 8 + 1) ?hr1 ?hr2 ?hr3 ?hn ?hp ?hsp ?h29 ?h28 ?h18 ?hm72 ?hm64 ?hal ?hbd ?hpacc ?hwa
    ?hlen ?hstr ?hF1
  case hr0' => simp [setReg]
  case hr5 => simp [setReg]
  case hr1 => simp [setReg, BitVec.ofNat_add]
  case hr2 => simp [setReg]
  case hr3 => simp [setReg]
  case hn => omega
  case hp => omega
  case hsp => rfl
  case h29 => simpa [setReg] using h29
  case h28 => simpa [setReg] using h28
  case h18 => simpa [setReg] using h18
  case hm72 =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hm72
  case hm64 =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hm64
  case hal => exact hal
  case hbd => omega
  case hpacc =>
    rw [← hF1.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hoacc) (by omega) (by omega)
  case hwa =>
    simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact hwa
  case hlen => exact (erlp_pmf s S1 z obj bl hzn hbl hb8 hb256 hzr hdz).1
  case hstr => exact (erlp_pmf s S1 z obj bl hzn hbl hb8 hb256 hzr hdz).2
  case hF1 =>
    janus_frame

end Fv256.Arm64.EncodeRLP
