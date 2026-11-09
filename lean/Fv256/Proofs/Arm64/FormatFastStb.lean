import Extracted
import Fv256.Proofs.Common.FormatFastDefsA64
import Fv256.Proofs.Common.FormatFastFactsA64
import Fv256.Proofs.Arm64.DecExt
import Fv256.Proofs.Common.GrabTac

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.E

namespace Fv256.Arm64.FormatFast

theorem roundupsize_pos_small : ∀ n, n < 79 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

set_option janus.callRegions true in
/-- the `d/v/s` path: `stringtoslicebyte(nil, s)` from `Format+0x14c`, return at `Format+0x15c` -/
theorem stb_dec (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len : Nat)
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x14c))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4096 : 4096 ≤ stack) (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h1 : S.regs 1 = BitVec.ofNat 64 len)
    (hso : StrOut S.mem ptr len bs) (hdis : ptr + len ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ ptr)
    (hlen1 : 1 ≤ len) (hlen : len ≤ 78) (h32 : 32 ≤ ptr)
    (hH : H [0, ptr, len] (S0.regs 28).toNat S0.sp.toNat (rtView rt S.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x15c)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧
        ∃ r0 r1 r2 : Nat, S'.regs 0 = BitVec.ofNat 64 r0 ∧ S'.regs 1 = BitVec.ofNat 64 r1 ∧ S'.regs 2 = BitVec.ofNat 64 r2 ∧
          r1 = len ∧ 0 < r2 ∧ r2 < 2 ^ 64 ∧ InRanges r0 r2 rt ∧ BytesHold S'.mem r0 r1 r2 bs) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hso
  janus_run [h0, h1, hwa, hH, hs2, hs3, hs4, h32, i4] until [Extracted.entry + 0x15c] calls [hc2]
  rename_i r0 r1 r2 junk f v m ex ep hfr hTB
  obtain ⟨hr1, -, hbig⟩ := hTB
  obtain ⟨hr2, hpos⟩ := hbig (Or.inl rfl)
  have hrp := roundupsize_pos_small bs.length (by omega) (by omega)
  obtain ⟨hIn, hBH⟩ := hpos (by omega)
  refine ReachesRet.done ?_ ⟨?_, r0.toNat, r1.toNat, r2.toNat, by simp [retStateX, callRegs_apply, setReg_apply],
    by simp [retStateX, callRegs_apply, setReg_apply], by simp [retStateX, callRegs_apply, setReg_apply], by omega, ?_, r2.isLt, hIn, hBH⟩
  · simp [retStateX, Extracted.entry, setReg_apply]
  · refine finv_call_k (e := S0.sp.toNat + 8 + 24) (k := 4096) (m := m) hi' hst hout h4096 (by omega) hfr ?_ ?_ ?_ ?_ (by simp [retStateX])
    all_goals simp [retStateX, setReg_apply, callRegs_apply, i4, i29, i28, i18]
  · omega

end Fv256.Arm64.FormatFast
