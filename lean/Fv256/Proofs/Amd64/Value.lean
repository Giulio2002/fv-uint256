import Extracted
import Fv256.Proofs.Amd64.CallSites.Live
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE
import Fv256.Proofs.Common.StrE
import Fv256.Proofs.Common.SpecTxt
import Fv256.Proofs.Common.GrabTac
import Fv256.Proofs.Common.LinkEq
import Fv256.Proofs.Amd64.DecExt
import Fv256.Proofs.Amd64.DecExtGen
import Fv256.Proofs.Arm64.SbtsG
import Fv256.Proofs.Amd64.SbtsG
import Janus.Contracts.IfaceLive
import Fv256.Spec.Amd64.Value

/-!
# `(*uint256.Int).Value() (driver.Value, error)` (amd64): the interface value holding the string `Dec(z)`, error nil

As the arm64 theorem (`Fv256.Arm64.Value`), over the live runtime `R`: the call returns `(type, data, err)`: `RAX` the type descriptor of
`string`, `RBX` a box inside the runtime ranges holding the header `(p, l)` of a string whose bytes are `Dec(z)`, `RCX = RDI = 0` (nil error).
Contracts: the live `slicebytetostring` (used by `Dec`) and the live `convTstring`; the second-call hypothesis ranges over the live-runtime
state (`R.inv` for a live set `L1` and budget `b1`) that the first call leaves.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec
open Fv256.Amd64.SbtsG

namespace Fv256.Amd64.Value

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (R : RtInv) (z : BitVec 64)
    (hc0 : RtLiveContract64 (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)
    (hc2 : RtLiveContract64 (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 4600 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ StackWritable s 4600 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4600) (4600 + 8) R.rt ∧ Outside 5163273 256 R.rt ∧ Outside 5176582 256 R.rt ∧ Outside 5134938 256 R.rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          HL R [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          HL R [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
          (s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem M [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
          DecAt R.rt 5163273 5176582 5134938 p l →
          (100 ≤ s.mem.readLE z.toNat 32 →
            R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 14).toNat M
              (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
            (InRanges p l R.rt → InRanges p l L)))
      (fun s s' => s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' R.rt s'.mem (s'.regs 3).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (valueAt s z 32))) ∧
        s'.regs 1 = 0 ∧ s'.regs 7 = 0 ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hgo, hw, hd, hout, hrt1, hrt2, hrt3, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1, hLive⟩
  janus64_intro hs
  have hHG : 2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      HG64 R ssAddr 16 (s.regs 14).toNat
        [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem) := fun h => ⟨rfl, hH h⟩
  have hHG1 : 100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      HG64 R ssAddr 16 (s.regs 14).toNat
        [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem) := fun h h' => ⟨rfl, hH1 h h'⟩
  clear hH hH1
  have hdE : decE = 4931168 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run [hdE] until [4931123] calls [dec_summary_ext_gen impl R.rt (HG64 R ssAddr 16 (s.regs 14).toNat) z
    (Fv256.Arm64.SbtsG.Gp R (s.regs 14).toNat 16) (fun r0 r1 m m' h => Fv256.Arm64.SbtsG.Gp_congr R _ _ r0 r1 h)
    (contract_G64 hc0 (s.regs 14).toNat 16)]
  grab_last_const Janus.MemFrame as hFRimp
  have hFR : MemFrame ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 32) 8 4931123) s'.mem
      (R.rt ++ [((s.regs 4).toNat - 32 - 4568, (s.regs 4).toNat - 32 + 8)]) := by assumption
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  grab_const Fv256.Arm64.SbtsG.Gp as hGi
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  have hW : MemFrame s.mem ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 32) 8 4931123)
      (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) := by
    refine MemFrame.trans (rs := R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])
      (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
      (MemFrame.of_writeLE _ _ (rs := R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
    intro a n h; exact ⟨h, h⟩
  have hMF : MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) := by
    have h2 := MemFrame.mono (rs' := R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) hFR (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, trivial⟩)
    exact hW.trans h2 fun a n h => ⟨h, h⟩
  simp (disch := omega) only [valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hl1 hl2 hl3 hl4 hFRimp hGi
  have hSO' : StrOut s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) (decBytes (s.mem.readLE z.toNat 32)) :=
    ⟨hl1, hl2, fun h => by rw [hMF.accessible]; exact hl3 h, hl4⟩
  have hMFs : s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem s'.mem [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)] := by
    intro hlt
    have h1 : MemFrame s.mem ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 32) 8 4931123)
        [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)] := by
      refine MemFrame.trans (rs := [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)])
        (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)) (List.mem_singleton_self _) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)) (List.mem_singleton_self _) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) (hFRimp hlt) (fun a n h => by
      simp only [outside_cons, outside_nil, Outside, and_true] at h ⊢
      omega)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  obtain ⟨L, b, hLA, hLs⟩ : ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R cvAddr [(s'.regs 0).toNat, (s'.regs 3).toNat] L b (convTstringLive.cost [(s'.regs 0).toNat, (s'.regs 3).toNat] s'.mem)
        (s.regs 14).toNat s'.mem (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
      (InRanges (s'.regs 0).toNat (s'.regs 3).toNat R.rt → InRanges (s'.regs 0).toNat (s'.regs 3).toNat L) := by
    by_cases h100 : 100 ≤ s.mem.readLE z.toNat 32
    · obtain ⟨L1, b1, h1, h2, h3⟩ := hGi h100
      exact hLive s'.mem _ _ L1 b1 hMF hMFs hSO' hDA (fun _ => ⟨h1, h2, h3⟩)
    · exact hLive s'.mem _ _ [] 0 hMF hMFs hSO' hDA (fun h => absurd h h100)
  obtain ⟨hok, hinv, hcost, hsep1, hsep2⟩ := hLA
  have hguard : s'.mem.readLE (BitVec.toNat (s.regs 14) + 16) 8 = s.mem.readLE (BitVec.toNat (s.regs 14) + 16) 8 := by
    refine MemFrame.readLE hMF _ _ ?_
    simp only [outside_append, outside_cons, outside_nil, Outside, and_true]
    refine ⟨hgo, by omega⟩
  have hcost' : (if BitVec.toNat (s'.regs 3) = 0 then 0 else 16) ≤ b := by
    simpa [convTstringLive] using hcost
  have hsep1' : LiveSep L ([((s.regs 4).toNat - 32 - 4096, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 32 + 8, (s.regs 4).toNat - 32 + 8 + 16)] ++
      [((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)]) := hsep1
  have hsep2' : LiveSep ([((s.regs 4).toNat - 32 - 4096, (s.regs 4).toNat - 32), ((s.regs 4).toNat - 32 + 8, (s.regs 4).toNat - 32 + 8 + 16)] ++
      [((s.regs 4).toNat - 32, (s.regs 4).toNat - 32 + 8)]) R.rt := hsep2
  janus64_run calls [hc2 L b]
  have hdL := Fv256.LinkEq.DataLoaded.of_subset hLib.data hd
  have hj1 := dataLoaded_disjoint hdL digits_mem hwa
  have hj2 := dataLoaded_disjoint hdL smalls_mem hwa
  have hj3 := dataLoaded_disjoint hdL zeroDat_mem hwa
  rw [digits_base, digits_len] at hj1
  rw [smalls_base, smalls_len] at hj2
  rw [zeroDat_base, zeroDat_len] at hj3
  have hvlt : s.mem.readLE z.toNat 32 < 2 ^ 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  have hlpos : 0 < BitVec.toNat (s'.regs 3) := by
    have := decLen_pos (s.mem.readLE z.toNat 32)
    have h1 := hSO'.1
    have hlen : (decBytes (s.mem.readLE z.toNat 32)).length = decLen (s.mem.readLE z.toNat 32) := rfl
    omega
  rename_i b0 b1 b2 b3 b4 b5 b6 M2 b8 b9 hF2' hBx hLF' hFr hAp hInv
  simp only [if_neg (show ¬ BitVec.toNat (s'.regs 3) = 0 by omega)] at hBx
  have hMF2 : MemFrame s.mem M2 (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) := by
    have h2 := MemFrame.mono (rs' := R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) hF2' (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      exact ⟨h1, by omega, by omega, trivial⟩)
    have h1 : MemFrame s'.mem (Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 32) 8 4931128)
        (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) :=
      MemFrame.of_writeLE s'.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
    exact hMF.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩
  have hOut : BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 3) ≤ BitVec.toNat (s.regs 4) - 4600 ∨
      BitVec.toNat (s.regs 4) + 8 ≤ BitVec.toNat (s'.regs 0) := by
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := MemFrame.outside_mem hout hr
      omega
    all_goals omega
  have hbase : Spec.strBytes (Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 32) 8 4931128) (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) =
      Spec.strBytes s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) :=
    Janus.Spec.strBytes_congr (fun i hi => Janus.Arm64.Memory.bytes_writeLE_outside s'.mem (by omega))
  have hbytes : Spec.strBytes M2 (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) =
      Spec.strBytes s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) := by
    refine Eq.trans ?_ hbase
    have hout2 : ∀ t, (t = 5163273 ∨ t = 5176582 ∨ t = 5134938) → Outside t 256 R.rt →
        BitVec.toNat (s'.regs 0) ≥ t → BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 3) ≤ t + 256 →
        Outside (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3))
          (R.rt ++ [(BitVec.toNat (s.regs 4) - 32 - 4096, BitVec.toNat (s.regs 4) - 32),
            (BitVec.toNat (s.regs 4) - 32 + 8, BitVec.toNat (s.regs 4) - 32 + 8 + 16)]) := by
      intro t ht hr h1 h2
      simp only [outside_append, outside_cons, outside_nil]
      refine ⟨Outside.of_sub hr (by omega) (by omega), by omega, by omega, trivial⟩
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hin := hLs ⟨r, hr, h1, h2⟩
      apply Janus.Spec.strBytes_congr
      intro i hi
      have := hLF'.readLE_nil (BitVec.toNat (s'.regs 0) + i) 1 (by
        obtain ⟨r', hr', k1, k2⟩ := hin
        exact ⟨r', hr', by omega, by omega⟩)
      rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
      exact BitVec.eq_of_toNat_eq this
    · exact strBytes_of_frame hF2' (hout2 5163273 (Or.inl rfl) hrt1 h1 h2)
    · exact strBytes_of_frame hF2' (hout2 5176582 (Or.inr (Or.inl rfl)) hrt2 h1 h2)
    · exact strBytes_of_frame hF2' (hout2 5134938 (Or.inr (Or.inr rfl)) hrt3 h1 h2)
  have hSO2 := hSO'
  refine ⟨rfl, ⟨BitVec.toNat (s'.regs 0), BitVec.toNat (s'.regs 3), hBx, ?_⟩, ?_⟩
  · obtain ⟨hs1, hs2, -, hs4⟩ := hSO2
    refine ⟨?_, hs2, fun h => ?_, by simp only [valueAt]; rw [hbytes]; exact hs4⟩
    · simpa [valueAt] using hs1
    · first | exact hl3 h | (rw [hF2'.accessible, hMF.accessible]; exact hl3 h)
  · exact hMF2


namespace Witness

open Janus.Contracts.Toy Janus.Contracts.LiveStubAmd64

def tys : Tys := []
def okW : Nat → List Nat → Prop := fun a args =>
  (a = ssAddr ∧ ∃ ptr, args = [0, ptr, 16]) ∨ (a = cvAddr ∧ ∃ p, args = [p, 16])
def RW : RtInv := toyR tys okW

/-- the live stubs: `slicebytetostring` copying the 16 digits into a fresh block, `convTstring` boxing the string header -/
def implAt : List Amd64.Segment := [sbtsSeg64 ssAddr 16 16, convTstringSeg cvAddr 16]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem hok0 : ∀ args, okW ssAddr args → ∃ ptr, args = [0, ptr, 16] := by
  intro args h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exfalso; revert h; decide

theorem hok2 : ∀ args, okW cvAddr args → ∃ p, args = [p, 16] := by
  intro args h
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · exfalso; revert h; decide
  · exact h

set_option maxHeartbeats 4000000 in
theorem hc0 : RtLiveContract64 (Extracted.program.link implAt) ssAddr 4096 RW
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive := by
  rw [linked_eq]
  janus64_live_sbts 16 16 hok0

set_option maxHeartbeats 4000000 in
theorem hc2 : RtLiveContract64 (Extracted.program.link implAt) cvAddr 4096 RW convTstringSpec convTstringLive := by
  rw [linked_eq]
  janus64_live_convtstring 16 16 hok2

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

/-- `z = 10^15` (sixteen digits, a size class) at `zp`; the bump pointer cell holds `HEAP`; the return address `ret` at `[RSP]` -/
def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zp + 1 then 0x80 else if a = zp + 2 then 0xc6 else if a = zp + 3 then 0xa4 else
  if a = zp + 4 then 0x7e else if a = zp + 5 then 0x8d else if a = zp + 6 then 0x03 else
  if a = BUMP + 3 then 0x10 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4600, 4600 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩,
      ⟨BUMP, 8, true⟩, ⟨WBUF, 64, true⟩, ⟨HEAP, HSIZE, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem hz : s0.mem.readLE arg.toNat 32 = 1000000000000000 := by
  unfold s0 arg zp
  decide

theorem hdl : decLen 1000000000000000 = 16 := by
  simp (disch := omega) [decLen_ge, decLen_lt]

theorem bytes_heap (i : Nat) (hi : HEAP ≤ i) (hi' : i < HEND) : bytes i = 0 := by
  have h1 : ∀ d ∈ dsegs, d.base + d.bytes.length < HEAP := by
    unfold dsegs HEAP; decide +kernel
  have h2 : dsegs.find? (fun d => decide (d.base ≤ i ∧ i < d.base + d.bytes.length)) = none := by
    rw [List.find?_eq_none]
    intro d hd
    have := h1 d hd
    simp only [decide_eq_true_eq]; omega
  simp only [HEAP, HEND, HSIZE] at hi hi'
  unfold bytes
  simp only [zp, BUMP, sp0]
  have n0 : ¬ i = 1048576 + 2 := by omega
  have n1 : ¬ i = 198656 + 1 := by omega
  have n2 : ¬ i = 198656 + 2 := by omega
  have n3 : ¬ i = 198656 + 3 := by omega
  have n4 : ¬ i = 198656 + 4 := by omega
  have n5 : ¬ i = 198656 + 5 := by omega
  have n6 : ¬ i = 198656 + 6 := by omega
  have n7 : ¬ i = 4194304 + 3 := by omega
  simp only [n0, n1, n2, n3, n4, n5, n6, n7, h2, if_false]

set_option maxRecDepth 100000 in
theorem s0_inv (b g : Nat) (hb : 64 * b ≤ HSIZE) : toyInv [] b [] g (view (toyRt []) [] s0.mem) :=
  toyInv_init hb (by decide) (fun i h1 h2 => bytes_heap i h1 h2) (by decide) (by decide) (by decide)

theorem inv_of_view {m : Janus.Arm64.Memory} (b g : Nat) (hb : 64 * b ≤ HSIZE) (h : rtView RW.rt m = rtView RW.rt s0.mem) :
    toyInv [] b [] g (view (toyRt []) [] m) := by
  have : view (toyRt []) [] m = view (toyRt []) [] s0.mem := by
    rw [view_nil, view_nil]; exact h
  rw [this]; exact s0_inv b g hb

set_option maxRecDepth 100000 in
theorem pre :
StackGuardOK s0 4600 ∧ Outside ((s0.regs 14).toNat + 16) 8 RW.rt ∧ StackWritable s0 4600 8 ∧ Extracted.program.DataLoaded s0.mem ∧
        Outside ((s0.regs 4).toNat - 4600) (4600 + 8) RW.rt ∧ Outside 5163273 256 RW.rt ∧ Outside 5176582 256 RW.rt ∧ Outside 5134938 256 RW.rt ∧
        (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
        (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4600 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
        ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4600 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s0.mem.readLE arg.toNat 32 →
          HL RW [0, (s0.regs 4).toNat - 32 - 0x178 + 86 + (98 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
            (s0.regs 14).toNat ((s0.regs 4).toNat - 32 - 0x178 - 8) (rtView RW.rt s0.mem)) ∧
        (100 ≤ s0.mem.readLE arg.toNat 32 → s0.mem.readLE arg.toNat 32 < 2 ^ 64 →
          HL RW [0, (s0.regs 4).toNat - 32 - 384 - 0x20 + (24 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
            (s0.regs 14).toNat ((s0.regs 4).toNat - 32 - 384 - 0x58) (rtView RW.rt s0.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s0.mem M (RW.rt ++ [((s0.regs 4).toNat - 4600, (s0.regs 4).toNat + 8)]) →
          (s0.mem.readLE arg.toNat 32 < 100 → MemFrame s0.mem M [((s0.regs 4).toNat - 4600, (s0.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s0.mem.readLE arg.toNat 32)) →
          DecAt RW.rt 5163273 5176582 5134938 p l →
          (100 ≤ s0.mem.readLE arg.toNat 32 →
            RW.inv b1 L1 (s0.regs 14).toNat (view RW.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt RW cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s0.regs 14).toNat M
              (window64 ((s0.regs 4).toNat - 32) 4096 2) ∧
            (InRanges p l RW.rt → InRanges p l L)) := by
  rw [hz, hdl]
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ?_, ⟨by decide, by decide, by decide⟩, dataLoaded,
    ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide, fun h => absurd h (by decide), ?_, ?_⟩
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · intro _ _ m hm
    refine ⟨[], 2 ^ 20, Or.inl ⟨rfl, _, rfl⟩, ?_, ?_, ?_, ?_⟩
    · exact inv_of_view _ (BitVec.toNat (s0.regs 14)) (by simp [HSIZE]) hm
    · have hr : roundupsize 16 true = 16 := by decide
      simp [slicebytetostringLive, arg, hr]
    · intro r hr; simp at hr
    · intro r hr
      simp only [window64, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil] <;> decide
  · intro M p l L1 b1 hMF _ hSO hDA hant
    obtain ⟨hinv, hb, hL⟩ := hant (by decide)
    have hl : l = 16 := by
      have h := hSO.1
      have h16 : (decBytes 1000000000000000).length = 16 := hdl
      omega
    subst hl
    have hinv' : toyInv [] b1 L1 (BitVec.toNat (s0.regs 14)) (view (toyRt []) L1 M) := hinv
    obtain ⟨p1, -, hH, -, -, hLs, -⟩ := hinv'
    refine ⟨L1, b1, ⟨Or.inr ⟨rfl, p, rfl⟩, hinv, ?_, ?_, ?_⟩, fun _ => hL (by omega)⟩
    · simp [convTstringLive]; omega
    · intro r hr
      have := hLs r hr
      have h4 : (s0.regs 4).toNat = 1048576 := by decide
      simp only [h4, window64, outside_cons, outside_nil, HEAP] at this ⊢
      exact ⟨by omega, by omega, by omega, trivial⟩
    · intro r hr
      simp only [window64, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil] <;> decide

-- CALLSITE-BLOCK Value
def csSb0 : Amd64.State :=
  { s0 with regs := fun i => if i = 0 then 0 else if i = 3 then arg else if i = 1 then 16 else if i = 4 then BitVec.ofNat 64 (sp0 - 416) else s0.regs i }
def csSb : Amd64.State := { csSb0 with rip := BitVec.ofNat 64 ssAddr }

theorem csSb_rip : csSb.rip = BitVec.ofNat 64 ssAddr := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre64 4096 RW (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 csSb := by
  have hrt : RW.rt = toyRt [] := rfl
  have hw : argWords64 csSb 3 = [0, zp, 16] := by
    unfold argWords64 csSb csSb0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · simp only [slicebytetostringSpec, hw, Contracts.arg, BufOK, StrIn]; exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, hw, ReadsOutside]; intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only [Contracts.arg, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, calleeStack64, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide
  · simp only [calleeStack64, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · show RW.ok ssAddr (argWords64 csSb 3); rw [hw]; exact Or.inl ⟨rfl, zp, by decide⟩
  · exact s0_inv 0x100000 (csSb.regs 14).toNat (by simp [HSIZE])
  · intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)

def csCv0 : Amd64.State :=
  { s0 with regs := fun i => if i = 0 then arg else if i = 3 then 16 else if i = 4 then BitVec.ofNat 64 (sp0 - 32) else s0.regs i }
def csCv : Amd64.State := { csCv0 with rip := BitVec.ofNat 64 cvAddr }

theorem csCv_rip : csCv.rip = BitVec.ofNat 64 cvAddr := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csCv_pre : RtLivePre64 4096 RW (convTstringSpec) convTstringLive cvAddr [] 0x100000 csCv := by
  have hrt : RW.rt = toyRt [] := rfl
  have hw : argWords64 csCv 2 = [zp, 16] := by
    unfold argWords64 csCv csCv0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · trivial
  · intro r hr; simp [convTstringSpec] at hr
  · simp only [calleeStack64, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · show RW.ok cvAddr (argWords64 csCv 2); rw [hw]; exact Or.inr ⟨rfl, zp, by decide⟩
  · exact s0_inv 0x100000 (csCv.regs 14).toNat (by simp [HSIZE])
  · intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)

/-- The preconditions, the `slicebytetostring` and `convTstring` live contracts (toy runtime serving both requests of the witness:
`z = 10^15`, sixteen digits) and the second-call hypothesis are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (R : RtInv) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtLiveContract64 (Extracted.program.link impl) ssAddr 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    RtLiveContract64 (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 4600 ∧ Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ StackWritable s 4600 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4600) (4600 + 8) R.rt ∧ Outside 5163273 256 R.rt ∧ Outside 5176582 256 R.rt ∧ Outside 5134938 256 R.rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4600 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          HL R [0, (s.regs 4).toNat - 32 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 32 - 0x178 - 8) (rtView R.rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          HL R [0, (s.regs 4).toNat - 32 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 32 - 384 - 0x58) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s.mem M (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
          (s.mem.readLE z.toNat 32 < 100 → MemFrame s.mem M [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
          DecAt R.rt 5163273 5176582 5134938 p l →
          (100 ≤ s.mem.readLE z.toNat 32 →
            R.inv b1 L1 (s.regs 14).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 14).toNat M
              (window64 ((s.regs 4).toNat - 32) 4096 2) ∧
            (InRanges p l R.rt → InRanges p l L))) ∧ 100 ≤ s.mem.readLE z.toNat 32 ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 ssAddr ∧ RtLivePre64 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 s_c) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 cvAddr ∧ RtLivePre64 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' R.rt s'.mem (s'.regs 3).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (valueAt s z 32))) ∧
        s'.regs 1 = 0 ∧ s'.regs 7 = 0 ∧
        MemFrame s.mem s'.mem (R.rt ++ [((s.regs 4).toNat - 4600, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt, RW, ret, s0, arg, hc0, hc2, ?w2, ?w3, pre, ?w5,
    ⟨csSb, csSb_rip, csSb_pre⟩,
    ⟨csCv, csCv_rip, csCv_pre⟩,
    correctness implAt RW arg hc0 hc2 ret ?w2 s0 ?w3 pre⟩
  case w2 => exact by rw [linked_eq]; exact hret
  case w3 => exact by rw [linked_eq]; exact setup
  case w5 => exact by rw [hz]; decide
end Witness

end Fv256.Amd64.Value
