import Extracted
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.GrabTac
import Fv256.LinkEq
import Fv256.Arm64.DecExt
import Janus.Contracts.IfaceLive

/-!
# `(*uint256.Int).Value() (driver.Value, error)` (arm64): the interface value holding the string `Dec(z)`, error nil

**Guarantee.** Go doc (sql.go): "Value implements the database/sql/driver Valuer interface": the decimal string of `z` as a `driver.Value`
(an interface holding a `string`), error `nil`.  The code calls `Dec` and then `runtime.convTstring` to box the string header.  Under the
contracts of `slicebytetostring` (used by `Dec`) and the **live** `convTstring` (`RtLiveContract … convTstringSpec convTstringLive`, over
the runtime invariant `R`) and the live-set hypothesis for the second call (over every memory that is a frame of the entry memory and
every string `(p, l)` that `Dec` can return, `DecAt`: some live set `L` and budget `b` serve the request, and a string `Dec` allocated is
in `L`), the call returns `(type, data, err)`: `X0` the type descriptor of `string`, `X1` a box inside the runtime ranges holding the
header `(p, l)` of a string whose bytes are `Dec(z)`, `X2 = X3 = 0` (nil error).
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec

namespace Fv256.Arm64.Value

abbrev cvAddr : Nat := Extracted.program.contractAddr "runtime.convTstring"

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (R : RtInv) (rt : List (Nat × Nat)) (hrt : R.rt = rt) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s (4096 + 32) ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 960826 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt rt 989280 1002589 960826 p l →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
              [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l rt → InRanges p l L)))
      (fun s s' => s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (val256 s.mem z.toNat))) ∧
        s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hgo, hst, hd, hout, hrt1, hrt2, hrt3, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hLive⟩
  subst hrt
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4640, hsp2, hwa⟩ := hst
  simp only [val256, Fv256.Util.readLE_32] at hH hH1 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [754556] calls [dec_summary_ext impl R.rt H z hc]
  grab_last_const Janus.MemFrame as hFR
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  have hMF : MemFrame s.mem s'.mem (R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) := by
    have h1 : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29)))
        (R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) := by
      refine MemFrame.trans (rs := R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)])
        (MemFrame.of_writeLE s.mem _ (r := (BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) (r := (BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) hFR (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, trivial⟩)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  have hSO' : StrOut s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 1)) (decBytes (val256 s.mem z.toNat)) := by
    simp only [val256, Fv256.Util.readLE_32, Nat.reducePow] at hl1 hl4 ⊢
    exact ⟨hl1, hl2, fun h => by rw [hMF.accessible]; exact hl3 h, hl4⟩
  obtain ⟨L, b, hLA, hLs⟩ := hLive s'.mem _ _ hMF hSO' hDA
  obtain ⟨hok, hinv, hcost, hsep1, hsep2⟩ := hLA
  have hguard : s'.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8 = s.mem.readLE (BitVec.toNat (s.regs 28) + 16) 8 := by
    refine MemFrame.readLE hMF _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, Outside, and_true]
    refine ⟨hgo, by omega⟩
  have hcost' : (if BitVec.toNat (s'.regs 1) = 0 then 0 else 16) ≤ b := by
    simpa [convTstringLive] using hcost
  janus_run calls [hc2 L b]
  grab_last_const Janus.LiveFrame as hLF
  grab_last_const Janus.MemFrame as hF2
  have hdL := Fv256.Arm64.LinkEq.DataLoaded.of_subset hLib.data hd
  have hj1 := dl_disjoint hdL digits_mem hwa
  have hj2 := dl_disjoint hdL smalls_mem hwa
  have hj3 := dl_disjoint hdL zeroDat_mem hwa
  rw [digits_base, digits_len] at hj1
  rw [smalls_base, smalls_len] at hj2
  rw [zeroDat_base, zeroDat_len] at hj3
  have hvlt : val256 s.mem z.toNat < 2 ^ 256 := by simpa [val256, Fv256.Util.readLE_32] using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  have hlpos : 0 < BitVec.toNat (s'.regs 1) := by
    have := decLen_pos (val256 s.mem z.toNat)
    have h1 := hSO'.1
    have hlen : (decBytes (val256 s.mem z.toNat)).length = decLen (val256 s.mem z.toNat) := rfl
    omega
  rename_i b0 b1 b2 b3 b4 b5 M2 b7 b8 hF2' hBx hLF' hFr hAp hInv
  simp only [if_neg (show ¬ BitVec.toNat (s'.regs 1) = 0 by omega)] at hBx
  have hMF2 : MemFrame s.mem M2 (R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) := by
    have h2 := MemFrame.mono (rs' := R.rt ++ [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) hF2' (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, by omega, by omega, trivial⟩)
    exact hMF.trans h2 fun a n h => ⟨h, h⟩
  have hbytes : strBytes M2 (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 1)) =
      strBytes s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 1)) := by
    have hout2 : ∀ t, (t = 989280 ∨ t = 1002589 ∨ t = 960826) → Outside t 256 R.rt →
        BitVec.toNat (s'.regs 0) ≥ t → BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 1) ≤ t + 256 →
        Outside (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 1))
          (R.rt ++ [(BitVec.toNat s.sp - 32 - 4096, BitVec.toNat s.sp - 32 - 8),
            (BitVec.toNat s.sp - 32 + 8, BitVec.toNat s.sp - 32 + 8 + 16)]) := by
      intro t ht hr h1 h2
      simp only [outside_append, outside_cons, outside_nil]
      refine ⟨Outside.of_sub hr (by omega) (by omega), by omega, by omega, trivial⟩
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hin := hLs ⟨r, hr, h1, h2⟩
      apply strBytes_congr
      intro i hi
      have := hLF'.readLE_nil (BitVec.toNat (s'.regs 0) + i) 1 (by
        obtain ⟨r', hr', k1, k2⟩ := hin
        exact ⟨r', hr', by omega, by omega⟩)
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
    · exact strBytes_of_frame hF2' (hout2 989280 (Or.inl rfl) hrt1 h1 h2)
    · exact strBytes_of_frame hF2' (hout2 1002589 (Or.inr (Or.inl rfl)) hrt2 h1 h2)
    · exact strBytes_of_frame hF2' (hout2 960826 (Or.inr (Or.inr rfl)) hrt3 h1 h2)
  have hSO2 := hSO'
  simp only [val256, Fv256.Util.readLE_32, Nat.reducePow] at hSO2
  refine ⟨rfl, ⟨BitVec.toNat (s'.regs 0), BitVec.toNat (s'.regs 1), hBx, ?_⟩, ?_⟩
  · obtain ⟨hs1, hs2, -, hs4⟩ := hSO2
    refine ⟨hs1, hs2, fun h => ?_, by rw [hbytes]; exact hs4⟩
    first | exact hl3 h | (rw [hF2'.accessible, hMF.accessible]; exact hl3 h)
  · exact hMF2

end Fv256.Arm64.Value
