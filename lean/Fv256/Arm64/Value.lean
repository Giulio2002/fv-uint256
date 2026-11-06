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

/-- the readiness the live `slicebytetostring` contract gives `Dec`'s single call -/
def HL (R : RtInv) : RtReady :=
  liveReady R.rt (LiveCallRt R ssAddr 4096 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (R : RtInv) (z : BitVec 64)
    (hc0 : RtLiveContract (Extracted.program.link impl) ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive)
    (hc2 : RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s (4096 + 32) ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt R.rt 989280 1002589 960826 p l →
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
  simp only [val256, Fv256.Util.readLE_32] at hH hH1 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [754556] calls [dec_summary_ext impl R.rt (HL R) z (hc0.ready rfl)]
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
  obtain ⟨L, b, hLA, hLs⟩ := hLive s'.mem _ _ hMF hMFs hSO' hDA
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
def okW : Nat → List Nat → Prop := fun a args => a = cvAddr ∧ ∃ p, args = [p, 2]
def RW : RtInv := toyR tys okW

def implAt : List Segment := [convTstringSeg cvAddr 16]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem hok : ∀ args, okW cvAddr args → ∃ p, args = [p, 2] := fun args h => h.2

/-- the runtime serves no `slicebytetostring` request (the `z = 10` call never makes one) -/
theorem hc0 : RtLiveContract (Extracted.program.link implAt) ssAddr 4096 RW
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive := by
  intro L b s hpc hpre
  obtain ⟨-, -, -, -, -, hokx, -⟩ := hpre
  exfalso
  have : ssAddr = cvAddr := hokx.1
  revert this
  decide

set_option maxHeartbeats 4000000 in
theorem hc2 : RtLiveContract (Extracted.program.link implAt) cvAddr 4096 RW convTstringSpec convTstringLive := by
  rw [linked_eq]
  janus_live_convtstring 2 16 hok

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = zp then 10 else
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
  sorry

theorem hz : val256 s0.mem arg.toNat = 10 := by
  unfold val256 s0 arg zp
  sorry

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 (4096 + 32) ∧ Outside ((s0.regs 28).toNat + 16) 8 RW.rt ∧ StackOK s0 4640 8 ∧ Extracted.program.DataLoaded s0.mem ∧
        Outside (s0.sp.toNat - 4640) (4640 + 8) RW.rt ∧ Outside 989280 256 RW.rt ∧ Outside 1002589 256 RW.rt ∧ Outside 960826 256 RW.rt ∧
        Ptr32 s0.mem arg false ∧ (arg.toNat + 32 ≤ s0.sp.toNat - 4640 ∨ s0.sp.toNat + 8 ≤ arg.toNat) ∧
        ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4640 ∨ s0.sp.toNat + 8 ≤ (s0.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s0.mem arg.toNat →
          HL RW [0, s0.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
            (s0.regs 28).toNat (s0.sp.toNat - 32 - 384) (rtView RW.rt s0.mem)) ∧
        (100 ≤ val256 s0.mem arg.toNat → val256 s0.mem arg.toNat < 2 ^ 64 →
          HL RW [0, s0.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
            (s0.regs 28).toNat (s0.sp.toNat - 32 - 384 - 96) (rtView RW.rt s0.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s0.mem M (RW.rt ++ [(s0.sp.toNat - 4640, s0.sp.toNat + 8)]) →
          (val256 s0.mem arg.toNat < 100 → MemFrame s0.mem M [(s0.sp.toNat - 4640, s0.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s0.mem arg.toNat)) →
          DecAt RW.rt 989280 1002589 960826 p l →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt RW cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s0.regs 28).toNat M
              [(s0.sp.toNat - 32 - 4096, s0.sp.toNat - 32 - 8), (s0.sp.toNat - 32 + 8, s0.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l RW.rt → InRanges p l L))
    := by
  sorry

/-- The preconditions, the `slicebytetostring` and `convTstring` live contracts (toy runtime serving only the `convTstring` request
of the witness) and the second-call hypothesis are jointly satisfiable (`z = 10`: the `v < 100` path; the `v >= 100` path is not witnessed). -/
theorem nonvacuous : ∃ (impl : List Segment) (R : RtInv) (ret : Nat) (s : State) (z : BitVec 64),
    RtLiveContract (Extracted.program.link impl) ssAddr 4096 R
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») slicebytetostringLive ∧
    RtLiveContract (Extracted.program.link impl) cvAddr 4096 R convTstringSpec convTstringLive ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s (4096 + 32) ∧ Outside ((s.regs 28).toNat + 16) 8 R.rt ∧ StackOK s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4640) (4640 + 8) R.rt ∧ Outside 989280 256 R.rt ∧ Outside 1002589 256 R.rt ∧ Outside 960826 256 R.rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4640 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          HL R [0, s.sp.toNat - 32 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384) (rtView R.rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          HL R [0, s.sp.toNat - 32 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 32 - 384 - 96) (rtView R.rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (R.rt ++ [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          (val256 s.mem z.toNat < 100 → MemFrame s.mem M [(s.sp.toNat - 4640, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt R.rt 989280 1002589 960826 p l →
          ∃ (L : List (Nat × Nat)) (b : Nat),
            LiveAt R cvAddr [p, l] L b (convTstringLive.cost [p, l] M) (s.regs 28).toNat M
              [(s.sp.toNat - 32 - 4096, s.sp.toNat - 32 - 8), (s.sp.toNat - 32 + 8, s.sp.toNat - 32 + 8 + 8 * 2)] ∧
            (InRanges p l R.rt → InRanges p l L))) := by
  sorry

end Witness

end Fv256.Arm64.Value
