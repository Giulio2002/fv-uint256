import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.Arm64.L10Defs

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Log10

set_option maxHeartbeats 64000000 in
theorem c0_47 (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧ Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧
        Tabs64 s.mem ∧ TabsBig s.mem ∧ Disjoint 1772992 160 (s.sp.toNat - 32) 32 ∧ Disjoint 1777472 1920 (s.sp.toNat - 32) 32 ∧
        s.mem.readLE (x.toNat + 24) 8 = 0 ∧ s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ 2 ^ 46 ≤ s.mem.readLE x.toNat 8 ∧ s.mem.readLE x.toNat 8 < 2 ^ 47)
      (fun s s' => 10 ^ (s'.regs 0).toNat ≤ val256 s.mem x.toNat ∧ val256 s.mem x.toNat < 10 ^ ((s'.regs 0).toNat + 1)) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, ⟨hx, hx'⟩, hdis, hT64, hTB, hd64, hdB, hz3, hz2, hz1, hl1, hl2⟩
  janus_intro hs
  simp only [Disjoint] at hdis hd64 hdB
  janus_data hd [hw]
  have hc : clzNat 64 (s.mem.readLE x.toNat 8) = 17 := by
    have := Util.clz_bl 64 (s.mem.readLE x.toNat 8) (Util.readLE8_lt s.mem _)
    have h2 : Spec.bitLen (s.mem.readLE x.toNat 8) = 47 := Util.bitLen_of_range _ 47 (by omega) (by omega) (by omega)
    omega
  have hTv : s.mem.readLE 1773104 8 = 100000000000000 := by simpa using hT64.2 14 (by decide)
  have hTa : s.mem.accessible 1773104 8 false = true := Memory.accessible_mono _ hT64.1 (by omega) (by omega)
  janus_run [hc, hTv, hz3, hz2, hz1]
  have := Util.readLE8_lt s.mem x.toNat
  have := Util.readLE8_lt s.mem (x.toNat + 8)
  have := Util.readLE8_lt s.mem (x.toNat + 16)
  have := Util.readLE8_lt s.mem (x.toNat + 24)
  all_goals omega

end Fv256.Arm64.Log10
