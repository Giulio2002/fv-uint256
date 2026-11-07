import Extracted
import Fv256.FormatFastDefs
import Fv256.FormatFastFacts
import Fv256.Amd64.DecExt
import Fv256.GrabTac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
open Fv256.FormatFast Fv256.E

namespace Fv256.Amd64.FormatFast

theorem roundupsize_pos_small : ∀ n, n < 79 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

set_option janus.callRegions true in
/-- the `d/v/s` path: `stringtoslicebyte(nil, s)` from `Format+0x145`, return at `Format+0x152` -/
theorem stb_dec (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (stack fW fP fF fWr : Nat)
    (z tab data : BitVec 64) (ch32 : Nat) (bs : List Nat) (ptr len : Nat)
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec)
    (S0 S : State) (hpc : S.rip = BitVec.ofNat 64 (Extracted.entry + 0x145))
    (hpre : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInvD rt stack z tab data ch32 S0 S)
    (h4096 : 4096 ≤ stack) (h0 : S.regs 0 = BitVec.ofNat 64 ptr) (h3 : S.regs 3 = BitVec.ofNat 64 len)
    (hso : StrOut S.mem ptr len bs) (hdis : ptr + len ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ ptr)
    (hlen1 : 1 ≤ len) (hlen : len ≤ 78) (h32 : 32 ≤ ptr)
    (hH : H [0, ptr, len] (S0.regs 14).toNat ((S0.regs 4).toNat - 8) (rtView rt S.mem)) :
    ReachesRet (Extracted.program.link impl) (BitVec.ofNat 64 (Extracted.entry + 0x152)) S
      (fun S' => FInvD rt stack z tab data ch32 S0 S' ∧
        ∃ r0 r1 r2 : Nat, S'.regs 0 = BitVec.ofNat 64 r0 ∧ S'.regs 3 = BitVec.ofNat 64 r1 ∧ S'.regs 1 = BitVec.ofNat 64 r2 ∧
          r1 = len ∧ 0 < r2 ∧ r2 < 2 ^ 64 ∧ InRanges r0 r2 rt ∧ BytesHold S'.mem r0 r1 r2 bs) := by
  obtain ⟨ht18, ht20, ht28, ht30, hta, hzr, hza, hwa⟩ := finvD_tab hpre hi
  have hi' := hi
  obtain ⟨i4, i5, i14, ix, ifr, i50, i58, i60, i68⟩ := hi
  obtain ⟨h0', h3', h1', h5, hal, hwb, hwn, hwa0, hout, hs58, hs60, hfW, hfP, hfF, hfWr, htb, hta0, hF, hP', hW', hWr', hto, htd, hzb, hza0, hzo, hzd⟩ := hpre
  have hwb0 := hwb
  have hout0 := hout
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hso
  janus64_run [h0, h3, hwa, hH, hs2, hs3, hs4, h32] until [Extracted.entry + 0x152] calls [hc2]
  rename_i r0 r1 r2 junk f x yh m zh kr hfr hTB
  obtain ⟨hr1, -, hbig⟩ := hTB
  obtain ⟨hr2, hpos⟩ := hbig (Or.inl rfl)
  have hrp := roundupsize_pos_small bs.length (by omega) (by omega)
  obtain ⟨hIn, hBH⟩ := hpos (by omega)
  have hfr' : MemFrame (S.mem.writeLE ((S0.regs 4).toNat - 8) 8 4923666) m
      (rt ++ [((S0.regs 4).toNat - 8 - stack, (S0.regs 4).toNat - 8), ((S0.regs 4).toNat - 8 + 8, (S0.regs 4).toNat - 8 + 8 + 24)]) :=
    MemFrame.mono hfr (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨h1, ?_, h3, trivial⟩ <;> omega)
  have h8 : 8 ≤ (S0.regs 4).toNat := by omega
  refine ReachesRet.done ?_ ⟨finvD_call hi' hwb0 hout0 (by omega) hfr' (by simp [retState64, callRegs64_apply, setRegF_apply, i4, sub_add8])
    (by simp [retState64, callRegs64_apply, setRegF_apply]) (by simp [retState64, callRegs64_apply, setRegF_apply])
    (by simp [retState64]) rfl, r0.toNat, r1.toNat, r2.toNat, by simp [retState64, callRegs64_apply],
    by simp [retState64, callRegs64_apply], by simp [retState64, callRegs64_apply], by omega, ?_, r2.isLt, hIn, hBH⟩
  · simp (disch := omega) only [retState64, retAddrOf, setRegF_apply, ite_true, sub8_toNat _ h8,
      Janus.Arm64.Memory.readLE_writeLE_self]
    simp [Extracted.entry]
  · omega

end Fv256.Amd64.FormatFast
