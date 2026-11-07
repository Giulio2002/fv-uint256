import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.DecExt
import Fv256.GrabTac
import Fv256.Arm64.FormatFastStb

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.FormatFastA64 Fv256.E

namespace Fv256.Arm64.FormatFast

/-- the `[2:]` offset arithmetic of the `x` path (arm64: `neg; asr #63; and #2`, as the stepper prints `asr`): for `3 ≤ len ≤ 66`
the added offset is `2` -/
theorem hexoff64 (n : Nat) (h1 : 3 ≤ n) (h2 : n ≤ 66) :
    (((if (0#64 - (BitVec.ofNat 64 n - 2#64)).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&&
        18446744073709551614 ||| ((0#64 - (BitVec.ofNat 64 n - 2#64)).rotateRight 63).toNat % 2) &&& 2) = 2 := by
  have key : ∀ k : Fin 64, (((if (0#64 - (BitVec.ofNat 64 (k.val + 3) - 2#64)).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&&
        18446744073709551614 ||| ((0#64 - (BitVec.ofNat 64 (k.val + 3) - 2#64)).rotateRight 63).toNat % 2) &&& 2) = 2 := by
    decide +kernel
  obtain ⟨k, hk⟩ : ∃ k : Fin 64, k.val + 3 = n := ⟨⟨n - 3, by omega⟩, by simp; omega⟩
  subst hk
  exact key k

set_option janus.callRegions true in
/-- the `x` path: `Hex(z)[2:]` and `stringtoslicebyte(nil, s)` from `Format+0x1a4`, return at `Format+0x1c8` -/
theorem stb_hex (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len : Nat)
    (hc2 : RtContract (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (S0 S : State) (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x1a4))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch32 S0 S)
    (h4096 : 4096 ≤ stack) (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h1 : S.regs 1 = BitVec.ofNat 64 len)
    (hlen3 : 3 ≤ len) (hlen : len ≤ 66) (hl : len - 2 = bs.length) (hbd : ptr + len ≤ 2 ^ 48)
    (hacc : 0 < len → S.mem.accessible ptr len false = true)
    (hbs : Janus.Spec.strBytes S.mem (ptr + 2) (len - 2) = bs)
    (hdis : ptr + len ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ ptr) (h32 : 32 ≤ ptr)
    (hH : H [0, ptr + 2, len - 2] (S0.regs 28).toNat S0.sp.toNat (rtView rt S.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x1c8)) S
      (fun S' => FInv rt stack z tab data ch32 S0 S' ∧
        ∃ r0 r1 r2 : Nat, S'.regs 0 = BitVec.ofNat 64 r0 ∧ S'.regs 1 = BitVec.ofNat 64 r1 ∧ S'.regs 2 = BitVec.ofNat 64 r2 ∧
          r1 = len - 2 ∧ 0 < r2 ∧ r2 < 2 ^ 64 ∧ InRanges r0 r2 rt ∧ BytesHold S'.mem r0 r1 r2 bs) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finv_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i29, i28, i18, ifr, i88, i96, i104, i112⟩ := hi
  obtain ⟨h0', h1', h2', h29', hal, hst, hwb, hwn, hwa0, hout, hs96, hs104, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzp, hzo, hzd⟩ := hpre
  have hacc2 : S.mem.accessible (ptr + 2) (len - 2) false = true :=
    Janus.Arm64.Memory.accessible_sub S.mem (hacc (by omega)) (Or.inl rfl) (by omega) (by omega)
  have hnz : 0 < len - 2 := by omega
  janus_run [h0, h1, hwa, hH, hacc2, hbs, h32, hbd, hexoff64 len hlen3 hlen, i4] until [Extracted.entry + 0x1c8] calls [hc2]
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
