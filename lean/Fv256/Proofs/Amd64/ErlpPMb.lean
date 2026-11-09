import Fv256.Proofs.Amd64.ErlpDefs
import Fv256.Proofs.Amd64.ErlpCall
import Fv256.Proofs.Common.RlpBytes

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

/-- the facts about the object that the `Write` call needs, over the abstract memory `S1.mem` -/
theorem erlp_pmf (s S1 : State) (z : BitVec 64) (obj bl stack : Nat) (hzn : z.toNat ≠ 0) (hwb : 56 + stack ≤ (s.regs 4).toNat)
    (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl) (hb256 : bl ≤ 256)
    (hzr : S1.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32)
    (hdj : (s.regs 4).toNat - 56 - stack + (stack + 88) ≤ obj ∨ obj + 48 ≤ (s.regs 4).toNat - 56 - stack)
    (hdz : z.toNat + 32 ≤ obj ∨ obj + 48 ≤ z.toNat)
    (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat) :
    (∀ v, (rlpBytes (rlpVal ((pmChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)).writeLE
        ((s.regs 4).toNat - 56) 8 v) z.toNat)).length = (bl + 7) / 8 + 1) ∧
    (∀ v, Janus.Spec.strBytes ((pmChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)).writeLE
        ((s.regs 4).toNat - 56) 8 v) (obj + (32 - (bl + 7) / 8)) ((bl + 7) / 8 + 1) =
      rlpBytes (rlpVal ((pmChain S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
        (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8)).writeLE
        ((s.regs 4).toNat - 56) 8 v) z.toNat)) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · rw [pm_rlpVal _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega), rlpVal, if_neg hzn, hzr,
      rlpBytes_length_multi _ (by omega), hbl]
  · rw [pm_rlpVal _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega), rlpVal, if_neg hzn, hzr, Util.readLE_32,
      pm_strOut _ _ _ _ _ _ _ _ _ (by omega) (by omega)]
    exact pm_str S1.mem obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8) (s.mem.readLE (z.toNat + 16) 8)
      (s.mem.readLE (z.toNat + 24) 8) ((bl + 7) / 8) _ (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
      (Util.readLE8_lt _ _) (by rw [← Util.readLE_32, hbl]; omega) (by rw [← Util.readLE_32, hbl]) (by omega) (by omega)
      (by omega)

set_option maxRecDepth 100000 in
/-- the path `8 ≤ bitlen`, second half: from the return of `newobject([33]byte)` (`EncodeRLP+0xc9`) to the return -/
theorem erlp_pmb (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R (WP z w))
    (s S1 : State) (h4104 : 4104 ≤ stack) (hfn : fn < 2 ^ 47)
    (hwb : 56 + stack ≤ (s.regs 4).toNat) (hwn : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hout : Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt)
    (hal : (s.regs 4).toNat % 8 = 0)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48)
    (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb8 : 8 ≤ bl) (hb256 : bl ≤ 256)
    -- the state after `newobject`
    (hpc : S1.rip = BitVec.ofNat 64 (Extracted.entry + 0xc9)) (obj : Nat) (hreg0 : S1.regs 0 = BitVec.ofNat 64 obj)
    (hin : InRanges obj 48 rt) (hob : obj + 48 ≤ 2 ^ 48) (hoacc : S1.mem.accessible obj 48 true = true)
    (hdj : (s.regs 4).toNat - 56 - stack + (stack + 88) ≤ obj ∨ obj + 48 ≤ (s.regs 4).toNat - 56 - stack)
    (hdz : z.toNat + 32 ≤ obj ∨ obj + 48 ≤ z.toNat) (hdt : tab.toNat + 24 + 8 ≤ obj ∨ obj + 48 ≤ tab.toNat + 24)
    (hr4 : S1.regs 4 = s.regs 4 - 48#64) (hr5 : S1.regs 5 = s.regs 4 - 8#64) (hr14 : S1.regs 14 = s.regs 14)
    (hx15 : S1.xmm 15 = s.xmm 15) (hdf : S1.df = s.df)
    (hm8 : S1.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) (hmr : S1.mem.readLE (s.regs 4).toNat 8 = ret)
    (hmz : S1.mem.readLE ((s.regs 4).toNat + 8) 8 = z.toNat) (hmbl : S1.mem.readLE ((s.regs 4).toNat - 16) 8 = bl)
    (hm16 : S1.mem.readLE ((s.regs 4).toNat + 16) 8 = tab.toNat) (hm24 : S1.mem.readLE ((s.regs 4).toNat + 24) 8 = w.toNat)
    (hr0 : S1.mem.readLE (z.toNat) 8 = s.mem.readLE (z.toNat) 8) (ha0 : S1.mem.accessible (z.toNat) 8 false = true)
    (hr1 : S1.mem.readLE (z.toNat + 8) 8 = s.mem.readLE (z.toNat + 8) 8) (ha1 : S1.mem.accessible (z.toNat + 8) 8 false = true)
    (hr2 : S1.mem.readLE (z.toNat + 16) 8 = s.mem.readLE (z.toNat + 16) 8) (ha2 : S1.mem.accessible (z.toNat + 16) 8 false = true)
    (hr3 : S1.mem.readLE (z.toNat + 24) 8 = s.mem.readLE (z.toNat + 24) 8) (ha3 : S1.mem.accessible (z.toNat + 24) 8 false = true)
    (hzr : S1.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32)
    (hfn' : S1.mem.readLE (tab.toNat + 24) 8 = fn) (hta : S1.mem.accessible (tab.toNat + 24) 8 false = true)
    (hwa : S1.mem.accessible ((s.regs 4).toNat - (56 + stack)) (56 + stack + 32) true = true)
    (hF1 : MemFrame s.mem S1.mem (rt ++ [((s.regs 4).toNat - 56 - 4096, (s.regs 4).toNat + 32)])) :
    Reaches ((Extracted.program.link impl).withExit ret) S1
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  have hnB := nB_bv bl hb256
  have hlen := pm_len _ bl _ hbl (by omega) hnB.symm.symm (by omega)
  have hStr := fun (m : Memory) (obj : Nat) => pm_str2 m obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
    (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) (s.mem.readLE z.toNat 32) bl _
    (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
    (Util.readLE_32 s.mem z.toNat) hbl (by omega) hnB (by omega)
  have hStr3 := fun (m : Memory) (obj : Nat) => pm_str3 m obj (s.mem.readLE z.toNat 8) (s.mem.readLE (z.toNat + 8) 8)
    (s.mem.readLE (z.toNat + 16) 8) (s.mem.readLE (z.toNat + 24) 8) (s.mem.readLE z.toNat 32) bl _
    (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _) (Util.readLE8_lt _ _)
    (Util.readLE_32 s.mem z.toNat) hbl (by omega) hnB (by omega)
  have hX := nB_bv2 bl hb256
  have hnB32 : (bl + 7) / 8 ≤ 32 := by omega
  have hDb := D_bv _ hnB32
  have hEb := E_bv _ hnB32
  janus64_run [hX, hDb, hEb, hzr, hr0, hr1, hr2, hr3, ha0, ha1, ha2, ha3, hzn, hm8, hmr, hmz, hmbl, hm16, hm24, hfn', hta, hwa]
    until [Extracted.entry + 0x14c]
  refine erlp_call impl rt fn stack R z tab w ret hret hw s _ h4104 hfn hwb hwn hout hzo hzd rfl ?hr0' ?hr2 (obj + (32 - (bl + 7) / 8))
    ((bl + 7) / 8 + 1) ?hr3 ?hr1 ?hr7 ?hn ?hp ?hr4 ?hr5 ?hr14 ?hx15 ?hdf ?hm8 ?hmr ?hwa ?hal ?hbd ?hpacc ?hlen ?hstr ?hF1
  case hr0' => simp [setRegF]
  case hr2 => simp [setRegF]
  case hr3 => simp [setRegF, BitVec.ofNat_add]
  case hr1 => simp [setRegF]
  case hr7 => simp [setRegF]
  case hn => omega
  case hp => omega
  case hr4 => simp [setRegF, hr4]
  case hr5 => simp [setRegF, hr5]
  case hr14 => simp [setRegF, hr14]
  case hx15 => simp [hx15]
  case hdf => simpa using hdf
  case hm8 =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hm8
  case hmr =>
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hmr
  case hwa =>
    simp only [Janus.Arm64.Memory.accessible_writeLE]
    exact hwa
  case hal => exact hal
  case hbd => omega
  case hpacc =>
    rw [← hF1.accessible]
    exact Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hoacc) (by omega) (by omega)
  case hlen =>
    intro v
    exact (erlp_pmf s S1 z obj bl stack hzn hwb hbl hb8 hb256 hzr hdj hdz hzd).1 v
  case hstr =>
    intro v
    exact (erlp_pmf s S1 z obj bl stack hzn hwb hbl hb8 hb256 hzr hdj hdz hzd).2 v
  case hF1 =>
    dsimp only
    janus_frame

end Fv256.Amd64.EncodeRLP
