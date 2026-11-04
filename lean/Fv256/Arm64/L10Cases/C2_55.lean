import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem c2_55 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint P64 P64sz (s.sp.toNat - 32) 32 ∧ Disjoint PB PBsz (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ 2 ^ 54 ≤ s.mem.readLE (x.toNat + 16) 8 ∧ s.mem.readLE (x.toNat + 16) 8 < 2 ^ 55)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hl1, hl2⟩
  janus_intro hs
  simp only [Tabs64, TabsBig, P64, P64sz, PB, PBsz, Extracted.dataAddr.«github.com/holiman/uint256.pows64», Extracted.dataSize.«github.com/holiman/uint256.pows64», Extracted.dataAddr.«github.com/holiman/uint256.pows», Extracted.dataSize.«github.com/holiman/uint256.pows»] at hT64 hTB hd64 hdB
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE (x.toNat + 16) 8) = 9 := by
    have := Util.clz_bl 64 (s.mem.readLE (x.toNat + 16) 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE (x.toNat + 16) 8) = 55 := Util.bitLen_of_range _ 55 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1778624 32 = 10000000000000000000000000000000000000000000000000000000 := by simpa using hTB.2 35 (by decide)
  have hTa : s.mem.accessible 1778624 32 false = true := Memory.accessible_mono _ hTB.1 (by omega) (by omega)
  obtain ⟨hT0, hT1', hT2', hT3'⟩ := Util.limbs_of_readLE32 s.mem 1778624 13150510911921848320 12898303124178706663 29387358770557187 0 (hTv.trans (by decide)) (by decide) (by decide) (by decide) (by decide)
  have hT1 : s.mem.readLE 1778632 8 = 12898303124178706663 := hT1'
  have hT2 : s.mem.readLE 1778640 8 = 29387358770557187 := hT2'
  have hT3 : s.mem.readLE 1778648 8 = 0 := hT3'
  janus_run [hc, hz3]
  all_goals (
    have := Util.readLE8_lt s.mem x.toNat
    have := Util.readLE8_lt s.mem (x.toNat + 8)
    have := Util.readLE8_lt s.mem (x.toNat + 16)
    have := Util.readLE8_lt s.mem (x.toNat + 24)
    simp only [Janus.Tactic.sub_flags_c, Janus.Tactic.awc_fst_toNat, Util.awc_c_dec, Util.dec_ite, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Nat.zero_add] at hbr
    repeat' split at hbr
    all_goals omega)

end Fv256.Arm64.Log10
