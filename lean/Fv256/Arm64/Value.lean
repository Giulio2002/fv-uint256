import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.UtilE64
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.GrabTac
import Fv256.LinkEq
import Fv256.Arm64.DecExt
import Fv256.Arm64.DecExtGen
import Fv256.Arm64.SbtsG
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

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Value

abbrev cvAddr : Nat := Extracted.program.contractAddr "runtime.convTstring"

/-- the readiness the live `slicebytetostring` contract needs at `Dec`'s single call: for every memory the runtime sees as `v`, the request is
served, the runtime invariant holds for some live set and a budget that covers the request and the `convTstring` request that follows
(16 bytes), and the call window is apart from the live set and the runtime ranges.  (The stack check is not part of it: it depends on memory
outside the runtime's view and is the `GuardOK` of the precondition.) -/
def HL (R : RtInv) : RtReady := fun a g sp v => ∀ m, rtView R.rt m = v →
  ∃ (L : List (Nat × Nat)) (b : Nat), LiveAt R ssAddr a L b (slicebytetostringLive.cost a m + 16) g m (windowAt sp 4096 3)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (R : RtInv) (z : BitVec 64)
    (hc0 : RtLiveContract (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)
    (hc2 : RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 4608 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt R.rt 989280 1002589 960826 p l →
          (100 ≤ val256 s.mem z.toNat →
            R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
              [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l R.rt → InRanges p l L)))
      (fun s s' => s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (val256 s.mem z.toNat))) ∧
        s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hgo, hst, hd, hout, hrt1, hrt2, hrt3, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hLive⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4640, hsp2, hwa⟩ := hst
  have hHG : 2 ^ 64 ≤ val256 s.mem z.toNat →
      Fv256.Arm64.SbtsG.HG R ssAddr 16 (s.regs 28).toNat
        [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem) := fun h => ⟨rfl, hH h⟩
  have hHG1 : 100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      Fv256.Arm64.SbtsG.HG R ssAddr 16 (s.regs 28).toNat
        [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem) := fun h h' => ⟨rfl, hH1 h h'⟩
  clear hH hH1
  simp only [val256, Fv256.Util.readLE_32] at hHG hHG1 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [754556] calls [dec_summary_ext_gen impl R.rt (Fv256.Arm64.SbtsG.HG R ssAddr 16 (s.regs 28).toNat) z
    (Fv256.Arm64.SbtsG.Gp R (s.regs 28).toNat 16) (fun r0 r1 m m' h => Fv256.Arm64.SbtsG.Gp_congr R _ _ r0 r1 h)
    (Fv256.Arm64.SbtsG.contract_G hc0 (s.regs 28).toNat 16)]
  grab_last_const Janus.MemFrame as hFRimp
  have hFR : MemFrame ((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29))) s'.mem
      (R.rt ++ [(BitVec.toNat s.sp - 32 - 4608, BitVec.toNat s.sp - 32 - 8)]) := by assumption
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
  have hMFs : val256 s.mem z.toNat < 100 → MemFrame s.mem s'.mem [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)] := by
    intro hlt
    have h1 : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 32) 8 ret).writeLE (BitVec.toNat s.sp - 40) 8 (BitVec.toNat (s.regs 29)))
        [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)] := by
      refine MemFrame.trans (rs := [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)])
        (MemFrame.of_writeLE s.mem _ (r := (BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)) (List.mem_singleton_self _) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) (r := (BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)) (List.mem_singleton_self _) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := [(BitVec.toNat s.sp - 4640, BitVec.toNat s.sp + 8)]) (hFRimp (by simpa [val256, Fv256.Util.readLE_32] using hlt)) (fun a n h => by
      simp only [outside_cons, outside_nil, Outside, and_true] at h ⊢
      omega)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  grab_const Fv256.Arm64.SbtsG.Gp as hGi
  obtain ⟨L, b, hLA, hLs⟩ : ∃ (L : List (Nat × Nat)) (b : Nat),
      LiveAt R cvAddr [(s'.regs 0).toNat, (s'.regs 1).toNat] L b (convTstringLive.cost [(s'.regs 0).toNat, (s'.regs 1).toNat] s'.mem)
        (s.regs 28).toNat s'.mem [(BitVec.toNat s.sp - 32 - 4096, BitVec.toNat s.sp - 32 - 8),
          (BitVec.toNat s.sp - 32 + 8, BitVec.toNat s.sp - 32 + 8 + 8 * 2)] ∧
      (InRanges (s'.regs 0).toNat (s'.regs 1).toNat R.rt → InRanges (s'.regs 0).toNat (s'.regs 1).toNat L) := by
    by_cases h100 : 100 ≤ s.mem.readLE z.toNat 32
    · obtain ⟨L1, b1, h1, h2, h3⟩ := hGi (by simpa [val256, Fv256.Util.readLE_32] using h100)
      exact hLive s'.mem _ _ L1 b1 hMF hMFs hSO' hDA (fun _ => ⟨h1, h2, h3⟩)
    · exact hLive s'.mem _ _ [] 0 hMF hMFs hSO' hDA (fun h => absurd (by simpa [val256, Fv256.Util.readLE_32] using h) h100)
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


namespace Witness

open Janus.Contracts.Toy Janus.Contracts.LiveStub

def tys : Tys := []
def okW : Nat → List Nat → Prop := fun a args =>
  (a = ssAddr ∧ ∃ ptr, args = [0, ptr, 16]) ∨ (a = cvAddr ∧ ∃ p, args = [p, 16])
def RW : RtInv := toyR tys okW

/-- the live stubs: `slicebytetostring` copying the 16 digits into a fresh block, `convTstring` boxing the string header -/
def implAt : List Segment := [sbtsSeg ssAddr 16 16, convTstringSeg cvAddr 16]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
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
theorem hc0 : RtLiveContract (Extracted.program.link implAt) ssAddr 4096 RW
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive := by
  rw [linked_eq]
  janus_live_sbts 16 16 hok0

set_option maxHeartbeats 4000000 in
theorem hc2 : RtLiveContract (Extracted.program.link implAt) cvAddr 4096 RW convTstringSpec convTstringLive := by
  rw [linked_eq]
  janus_live_convtstring 16 16 hok2

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

/-- `z = 10^15` (sixteen digits, a size class) at `zp`; the bump pointer cell holds `HEAP` -/
def bytes (a : Nat) : Byte :=
  if a = zp + 1 then 0x80 else if a = zp + 2 then 0xc6 else if a = zp + 3 then 0xa4 else
  if a = zp + 4 then 0x7e else if a = zp + 5 then 0x8d else if a = zp + 6 then 0x03 else
  if a = BUMP + 3 then 0x10 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4640, 4640 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩,
      ⟨BUMP, 8, true⟩, ⟨WBUF, 64, true⟩, ⟨HEAP, HSIZE, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide +kernel

theorem hz : val256 s0.mem arg.toNat = 1000000000000000 := by
  unfold val256 s0 arg zp
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
  simp only [zp, BUMP, HEAP, HEND, HSIZE] at hi hi'
  unfold bytes
  simp only [zp, BUMP]
  have n1 : ¬ i = 198656 + 1 := by omega
  have n2 : ¬ i = 198656 + 2 := by omega
  have n3 : ¬ i = 198656 + 3 := by omega
  have n4 : ¬ i = 198656 + 4 := by omega
  have n5 : ¬ i = 198656 + 5 := by omega
  have n6 : ¬ i = 198656 + 6 := by omega
  have n7 : ¬ i = 4194304 + 3 := by omega
  simp only [n1, n2, n3, n4, n5, n6, n7, h2, if_false]

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
GuardOK s0 4608 ∧ Outside ((s0.regs 28).toNat + 16) 8 RW.rt ∧ StackOK s0 4640 8 ∧ Extracted.program.DataLoaded s0.mem ∧
        Outside (s0.sp.toNat - 4640) (4640 + 8) RW.rt ∧ Outside 989280 256 RW.rt ∧ Outside 1002589 256 RW.rt ∧ Outside 960826 256 RW.rt ∧
        Ptr32 s0.mem arg false ∧ (arg.toNat + 32 ≤ s0.sp.toNat - 4640 ∨ s0.sp.toNat + 8 ≤ arg.toNat) ∧
        ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4640 ∨ s0.sp.toNat + 8 ≤ (s0.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s0.mem arg.toNat →
          HL RW [0, s0.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
            (s0.regs 28).toNat (s0.sp.toNat - 32 - 384) (rtView RW.rt s0.mem)) ∧
        (100 ≤ val256 s0.mem arg.toNat → val256 s0.mem arg.toNat < 2 ^ 64 →
          HL RW [0, s0.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
            (s0.regs 28).toNat (s0.sp.toNat - 32 - 384 - 96) (rtView RW.rt s0.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s0.mem M (RW.rt ++ [(s0.sp.toNat - 4640, s0.sp.toNat + 8)]) →
          (val256 s0.mem arg.toNat < 100 → MemFrame s0.mem M [(s0.sp.toNat - 4640, s0.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s0.mem arg.toNat)) →
          DecAt RW.rt 989280 1002589 960826 p l →
          (100 ≤ val256 s0.mem arg.toNat →
            RW.inv b1 L1 (s0.regs 28).toNat (view RW.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt RW cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s0.regs 28).toNat M
              [(s0.sp.toNat - 32 - 4096, s0.sp.toNat - 32 - 8), (s0.sp.toNat - 32 + 8, s0.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l RW.rt → InRanges p l L)) := by
  rw [hz, hdl]
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨⟨by decide, by decide, by decide⟩, ?_, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, ?_, fun h => absurd h (by decide), ?_, ?_⟩
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · simp only [s0, g0, sp0]; decide
  · intro _ _ m hm
    refine ⟨[], 2 ^ 20, Or.inl ⟨rfl, _, rfl⟩, ?_, ?_, ?_, ?_⟩
    · exact inv_of_view _ (BitVec.toNat (s0.regs 28)) (by simp [HSIZE]) hm
    · have hr : roundupsize 16 true = 16 := by decide
      simp [slicebytetostringLive, arg, hr]
    · intro r hr; simp at hr
    · intro r hr
      simp only [windowAt, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil] <;> decide
  · intro M p l L1 b1 hMF _ hSO hDA hant
    obtain ⟨hinv, hb, hL⟩ := hant (by decide)
    have hl : l = 16 := by
      have h := hSO.1
      have h16 : (decBytes 1000000000000000).length = 16 := hdl
      omega
    subst hl
    have hinv' : toyInv [] b1 L1 (BitVec.toNat (s0.regs 28)) (view (toyRt []) L1 M) := hinv
    obtain ⟨p1, -, hH, -, -, hLs, -⟩ := hinv'
    refine ⟨L1, b1, ⟨Or.inr ⟨rfl, p, rfl⟩, hinv, ?_, ?_, ?_⟩, fun _ => hL (by omega)⟩
    · simp [convTstringLive]; omega
    · intro r hr
      have := hLs r hr
      simp only [outside_cons, outside_nil, s0, sp0, HEAP, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at this ⊢
      exact ⟨by omega, by omega, trivial⟩
    · intro r hr
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, s0, g0, sp0, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil] <;> decide

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/Value.lean
def csSb0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then 16 else s0.regs i }
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 416), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre 4096 RW (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 csSb := by
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]; exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]; intro r hr; simp at hr; subst hr; simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, Outside, calleeStack]; decide
  · simp only [calleeStack, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · exact Or.inl ⟨rfl, zp, by decide⟩
  · exact s0_inv _ _ (by simp [HSIZE])
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)

def csCv0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 zp else if i = 1 then 16 else s0.regs i }
def csCv : State := { csCv0 with sp := BitVec.ofNat 64 (sp0 - 32), pc := BitVec.ofNat 64 cvAddr }

set_option maxRecDepth 100000 in
theorem csCv_pre : RtLivePre 4096 RW (convTstringSpec) convTstringLive cvAddr [] 0x100000 csCv := by
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · trivial
  · intro r hr; simp [convTstringSpec] at hr
  · simp only [calleeStack, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · exact Or.inr ⟨rfl, zp, by decide⟩
  · exact s0_inv _ _ (by simp [HSIZE])
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)

/-- The preconditions, the `slicebytetostring` and `convTstring` live contracts (toy runtime serving both requests of the witness:
`z = 10^15`, sixteen digits, so `Dec` allocates the string through the live stub and the `convTstring` request follows) and the
second-call hypothesis are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (ret : Nat) (s : State) (z : BitVec 64),
    RtLiveContract (Extracted.program.link impl) ssAddr 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 4608 ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat) (L1 : List (Nat × Nat)) (b1 : Nat),
          MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt R.rt 989280 1002589 960826 p l →
          (100 ≤ val256 s.mem z.toNat →
            R.inv b1 L1 (s.regs 28).toNat (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0 < l → InRanges p l L1)) →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
              [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l R.rt → InRanges p l L))) ∧ 100 ≤ val256 s.mem z.toNat ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtLivePre 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ssAddr [] 0x100000 s_c) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 cvAddr ∧ RtLivePre 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = Extracted.dataAddr.«type:string#f88732b8» ∧
        (∃ p l, BoxWords' R.rt s'.mem (s'.regs 1).toNat [p, l] ∧ StrOut s'.mem p l (decBytes (val256 s.mem z.toNat))) ∧
        s'.regs 2 = 0 ∧ s'.regs 3 = 0 ∧
        MemFrame s.mem s'.mem (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) := by
  refine ⟨implAt, RW, ret, s0, arg, hc0, hc2, ?w2, ?w3, pre, ?w5,
    ⟨csSb, rfl, csSb_pre⟩,
    ⟨csCv, rfl, csCv_pre⟩,
    correctness implAt RW arg hc0 hc2 ret ?w2 s0 ?w3 pre⟩
  case w2 => exact by rw [linked_eq]; exact hret
  case w3 => exact by rw [linked_eq]; exact setup
  case w5 => exact by rw [hz]; decide
end Witness

end Fv256.Arm64.Value
