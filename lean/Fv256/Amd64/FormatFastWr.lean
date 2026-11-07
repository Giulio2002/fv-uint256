import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast

namespace Fv256.Amd64.FormatFast

/-- the `Write` call of the `d/v/s` path (`Format+0x152`: after `stringtoslicebyte`; the slice is `(RAX, RBX, RCX) = (ptr, len, cap)`),
the epilogue and the return -/
theorem wrd_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RWr : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len cap : Nat)
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr (FastWP data bs))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x152))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h3 : S.regs 3 = BitVec.ofNat 64 len) (h1 : S.regs 1 = BitVec.ofNat 64 cap)
    (hlen : len = bs.length) (hstr : Janus.Spec.strBytes S.mem ptr len = bs) (hbd : ptr + len ≤ 2 ^ 48)
    (hacc : 0 < len → S.mem.accessible ptr len false = true) (hcap : len ≤ cap) (hcap64 : cap < 2 ^ 64) (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47)
    (hdis : ptr + len ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ ptr) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
      (fun S' => S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
        S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧ S'.df = S0.df ∧ S'.fsBase = S0.fsBase ∧
        MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
        (∃ j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0', h3', h1', h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfWr
  have hr72 : S.mem.readLE ((S0.regs 4).toNat + 72) 8 = S0.mem.readLE ((S0.regs 4).toNat + 72) 8 :=
    ifr.readLE _ _ (out_fl2 (hout.of_sub (by omega) (by omega)) (by omega) (by omega))
  have hr64 : S.mem.readLE ((S0.regs 4).toNat + 64) 8 = S0.mem.readLE ((S0.regs 4).toNat + 64) 8 :=
    ifr.readLE _ _ (out_fl2 (hout.of_sub (by omega) (by omega)) (by omega) (by omega))
  have hbl : (S.mem.readLE ((S0.regs 4).toNat + 72) 8) < 2 ^ 64 := by
    simpa using Janus.Arm64.Memory.readLE_lt S.mem ((S0.regs 4).toNat + 72) 8
  janus64_run [i58, i60, ht30, hta, hwa, hr72, hr64, h0, h3, h1, hret47] calls [hWr]
  rename_i junk f x yh m zh kr hkeep hfr hR
  exact ⟨ifs.symm ▸ rfl, frame_call ifr hwb (by omega) hfr, _, _, _, hR⟩

/-- the `Write` call of the `d/v/s` path (`Format+0x1a7`: after `stringtoslicebyte`; the slice is `(RAX, RBX, RCX) = (ptr, len, cap)`),
the epilogue and the return -/
theorem wrh_call (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (stack fW fP fF fWr : Nat) (RWr : Res)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len cap : Nat)
    (hWr : ICallContract64 (Extracted.program.link impl) fWr 4 stack 80 rt (fun _ => []) RWr (FastWP data bs))
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x1a7))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h3 : S.regs 3 = BitVec.ofNat 64 len) (h1 : S.regs 1 = BitVec.ofNat 64 cap)
    (hlen : len = bs.length) (hstr : Janus.Spec.strBytes S.mem ptr len = bs) (hbd : ptr + len ≤ 2 ^ 48)
    (hacc : 0 < len → S.mem.accessible ptr len false = true) (hcap : len ≤ cap) (hcap64 : cap < 2 ^ 64) (hret47 : S0.mem.readLE ((S0.regs 4).toNat + 72) 8 < 2 ^ 47)
    (hdis : ptr + len ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ ptr) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 72) 8)) S
      (fun S' => S'.regs 4 = S0.regs 4 + 80#64 ∧ S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8) ∧
        S'.regs 14 = S0.regs 14 ∧ S'.xmm 15 = S0.xmm 15 ∧ S'.df = S0.df ∧ S'.fsBase = S0.fsBase ∧
        MemFrame S0.mem S'.mem (FL rt (S0.regs 4).toNat stack) ∧
        (∃ j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1)) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, idf, ifs, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0', h3', h1', h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  simp only [CodePtrOK64] at hfWr
  have hr72 : S.mem.readLE ((S0.regs 4).toNat + 72) 8 = S0.mem.readLE ((S0.regs 4).toNat + 72) 8 :=
    ifr.readLE _ _ (out_fl2 (hout.of_sub (by omega) (by omega)) (by omega) (by omega))
  have hr64 : S.mem.readLE ((S0.regs 4).toNat + 64) 8 = S0.mem.readLE ((S0.regs 4).toNat + 64) 8 :=
    ifr.readLE _ _ (out_fl2 (hout.of_sub (by omega) (by omega)) (by omega) (by omega))
  have hbl : (S.mem.readLE ((S0.regs 4).toNat + 72) 8) < 2 ^ 64 := by
    simpa using Janus.Arm64.Memory.readLE_lt S.mem ((S0.regs 4).toNat + 72) 8
  janus64_run [i58, i60, ht30, hta, hwa, hr72, hr64, h0, h3, h1, hret47] calls [hWr]
  rename_i junk f x yh m zh kr hkeep hfr hR
  exact ⟨ifs.symm ▸ rfl, frame_call ifr hwb (by omega) hfr, _, _, _, hR⟩

end Fv256.Amd64.FormatFast
