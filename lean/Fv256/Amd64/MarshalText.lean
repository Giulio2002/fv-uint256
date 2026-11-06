import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.Amd64.DecExt
import Fv256.GrabTac
import Fv256.LinkEq

/-!
# `(*uint256.Int).MarshalText() ([]byte, error)` (amd64): the decimal digits of `z`, error nil

**Guarantee.** Go doc: "MarshalText marshals using the decimal representation (compatible with big.Int)": `[]byte(z.Dec())`, `nil`.
The code calls `Dec` and then `runtime.stringtoslicebyte(nil, s)`.  Under the contracts of `slicebytetostring` (used by `Dec`)
and `stringtoslicebyte` and the readiness `H` of the runtime for the second call (a hypothesis over every memory that is a
frame of the entry memory and every string `(p, l)` that `Dec` can return: `DecAt`, bytes `decBytes z`), the call returns
`(ptr, len, cap)` with `len ≤ cap`, `[ptr, ptr+cap)` writable and holding the digits of `z` in its first `len` bytes and zero
after (`BytesHold`), the error `(RDI, RSI) = (0, 0)` (nil), and changes no byte outside the runtime ranges and the frame.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec

namespace Fv256.Amd64.MarshalText

abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

theorem roundupsize_pos_small : ∀ n, n < 79 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s (0x378 + 40) ∧ StackWritable s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4608) (4608 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4608 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 40 - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 40 - 384 - 0x58) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
          DecAt rt 5163273 5176582 5134938 p l →
          H [0, p, l] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt M)))
      (fun s s' => BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hout, hrt1, hrt2, hrt32, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1, hH2⟩
  janus64_intro hs
  have hdE : decE = 4931168 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run [hdE] until [4928640] calls [dec_summary_ext impl rt H z hc]
  grab_last_const Janus.MemFrame as hFR
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  have hdL := Fv256.LinkEq.DataLoaded.of_subset hLib.data hd
  have hj1 := dataLoaded_disjoint hdL digits_mem hwa
  have hj2 := dataLoaded_disjoint hdL smalls_mem hwa
  have hj3 := dataLoaded_disjoint hdL zeroDat_mem hwa
  rw [digits_base, digits_len] at hj1
  rw [smalls_base, smalls_len] at hj2
  rw [zeroDat_base, zeroDat_len] at hj3
  have hOut : BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 3) ≤ BitVec.toNat (s.regs 4) - 4608 ∨
      BitVec.toNat (s.regs 4) + 8 ≤ BitVec.toNat (s'.regs 0) := by
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := MemFrame.outside_mem hout hr
      omega
    all_goals omega
  have hrt32' : 32 ≤ BitVec.toNat (s'.regs 0) := by
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hrt32 r hr
      omega
    all_goals omega
  have hMF : MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) := by
    have h1 : MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 40) 8 4928627)
        (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) := by
      refine MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)])
        (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) hFR (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, trivial⟩)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  simp (disch := omega) only [valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hl1 hl2 hl3 hl4
  have hSO' : StrOut s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) (decBytes (s.mem.readLE z.toNat 32)) :=
    ⟨hl1, hl2, fun h => by rw [hMF.accessible]; exact hl3 h, hl4⟩
  have hH2' := hH2 s'.mem _ _ hMF hSO' hDA
  janus64_run calls [hc2]
  grab_last_const Janus.Contracts.ToBytesOut as hTB
  grab_last_const Janus.MemFrame as hF2
  obtain ⟨hlen, -, hbig⟩ := hTB
  rw [hl4] at hlen
  have hvlt : s.mem.readLE z.toNat 32 < 2 ^ 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  have hd78 : decLen (s.mem.readLE z.toNat 32) ≤ 78 :=
    decLen_le_of_lt_pow _ 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
  have hd1 := decLen_pos (s.mem.readLE z.toNat 32)
  have hlen' : (decBytes (s.mem.readLE z.toNat 32)).length = decLen (s.mem.readLE z.toNat 32) := rfl
  obtain ⟨hr2, hpos⟩ := hbig (Or.inl rfl)
  rw [hl4] at hr2
  have hrp := roundupsize_pos_small (decBytes (s.mem.readLE z.toNat 32)).length (by omega) (by omega)
  obtain ⟨-, hBH⟩ := hpos (by omega)
  rw [hl4] at hBH
  have h1 : MemFrame s'.mem (Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 40) 8 4928645)
      (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) :=
    MemFrame.of_writeLE s'.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
  have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) hF2 (fun a n h => by
    simp only [outside_append, outside_cons] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, by omega, by omega, trivial⟩)
  refine ⟨by simpa [valueAt] using hBH, ?_⟩
  exact hMF.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩

end Fv256.Amd64.MarshalText
