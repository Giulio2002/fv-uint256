import Extracted
import Fv256.FormatFastDefsA64
import Fv256.FormatFastFactsA64
import Fv256.Arm64.FormatNil
import Fv256.Arm64.FormatNilRodata
import Fv256.DecAt
import Fv256.IntoBigCommon
import Fv256.Arm64.FM.IntoBigDefs
import Fv256.SpecC
import Fv256.SpecE

/-!
# `Format` (arm64): the assembly precondition `PreF` and the transfer lemmas across the prefix

`PreF` is stated at the ENTRY state `s`.  The prefix (`FormatPrefix.prefix_nz` / `prefix_z`) runs to `S0` (entry `SP` - 80) and changes memory
only inside `PFL (SP)` = `[SP-88, SP-72)` (the saved `x29`, `x30`) and `[SP+16, SP+32)` (the spilled `x1`, `x2`).
Every memory fact of `FPre` / `NilPre` at `S0` is moved back to `s`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall Janus.Contracts.Iface
  Janus.Spec.Type Janus.Spec.Map
open Fv256.FormatFastA64 Fv256.Arm64.FormatNil Fv256.E

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace Fv256.Arm64.FormatTransfer

/-- the memory the prefix writes (`r` = the entry `SP`) -/
def PFL (r : Nat) : List (Nat × Nat) := [(r - 88, r - 72), (r + 16, r + 32)]

theorem pfl_out {r a n : Nat} : Outside a n (PFL r) ↔ ((a + n ≤ r - 88 ∨ r - 72 ≤ a) ∧ (a + n ≤ r + 16 ∨ r + 32 ≤ a)) := by
  simp [PFL]

/-- a range outside the window `[r-88-stack, r+40)` is untouched by the prefix -/
theorem rdW {m m' : Memory} {r stack a n : Nat} (hf : MemFrame m m' (PFL r)) (h : a + n ≤ r - 88 - stack ∨ r + 40 ≤ a) :
    m'.readLE a n = m.readLE a n :=
  hf.readLE a n (by rw [pfl_out]; omega)

/-- the common call facts (the hypotheses of `prefix_nz` / `prefix_z`) -/
def PreCommon (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  GuardOK s 0 ∧ s.sp.toNat % 16 = 0 ∧ 88 + stack ≤ s.sp.toNat ∧ s.sp.toNat + 40 ≤ 2 ^ 48 ∧
  s.mem.accessible (s.sp.toNat - 88 - stack) (stack + 128) true = true ∧
  Outside (s.sp.toNat - 88 - stack) (stack + 128) rt

/-- the entry facts of the fast / big side (`z ≠ 0`), the entry-state form of `FPre` -/
def PreFastE (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (s : State) : Prop :=
  CodePtrOK fW ∧ CodePtrOK fP ∧ CodePtrOK fF ∧ CodePtrOK fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  s.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ s.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  s.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ s.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x38 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ tab.toNat + 0x18) ∧
  Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ z.toNat)

/-- `FPre` at `S0` from the entry facts -/
theorem fpre_of {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {fW fP fF fWr : Nat} {s S0 : State}
    (hc : PreCommon rt stack s) (hf : PreFastE rt stack z tab data fW fP fF fWr s) (h8 : 8 ≤ stack)
    (hr0 : S0.regs 0 = z) (hr1 : S0.regs 1 = tab) (hr2 : S0.regs 2 = data) (hsp : S0.sp = s.sp - 80#64)
    (hr29 : S0.regs 29 = s.sp - 88#64)
    (h96 : S0.mem.readLE (s.sp.toNat - 80 + 96) 8 = tab.toNat) (h104 : S0.mem.readLE (s.sp.toNat - 80 + 104) 8 = data.toNat)
    (hfr : MemFrame s.mem S0.mem (PFL s.sp.toNat)) : FPre rt stack z tab data fW fP fF fWr S0 := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨c1, c2, c3, c4, t1, t2, t3, t4, t5, t6, t7, t8, z1, z2, z3⟩ := hf
  have hn : S0.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp, BitVec.toNat_sub]; have := s.sp.isLt; simp; omega
  have h29 : S0.regs 29 = S0.sp - 8#64 := by
    rw [hr29, hsp]; bv_omega
  refine ⟨hr0, hr1, hr2, h29, by omega, h8, by omega, by omega, ?_, ?_, ?_, ?_, c1, c2, c3, c4, t1, ?_, ?_, ?_, ?_, ?_, t7, ?_, ?_, z2, ?_⟩
  · rw [hn, show s.sp.toNat - 80 - stack = s.sp.toNat - 88 - stack + 8 by omega, hfr.accessible]
    exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [hn]; exact hout.of_sub (by omega) (by omega)
  · rw [hn]; exact h96
  · rw [hn]; exact h104
  · rw [hfr.accessible]; exact t2
  · rw [rdW (stack := stack) hfr (by omega)]; exact t3
  · rw [rdW (stack := stack) hfr (by omega)]; exact t4
  · rw [rdW (stack := stack) hfr (by omega)]; exact t5
  · rw [rdW (stack := stack) hfr (by omega)]; exact t6
  · rw [hn]; omega
  · exact ⟨by rw [hfr.accessible]; exact z1.1, z1.2⟩
  · rw [hn]; omega


/-- the window-wide frame of the fast side, in entry terms: `rt` and the whole window `[r-88-stack, r+40)` -/
def FLE (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) := rt ++ [(r - 88 - stack, r + 40)]

theorem fle_sub {rt : List (Nat × Nat)} {r stack : Nat} (h8 : 88 + stack ≤ r) {a n : Nat} (h : Outside a n (FLE rt r stack)) :
    Outside a n (PFL r) ∧ Outside a n (FL rt (r - 80) stack) := by
  simp only [FLE, FL, outside_append, outside_cons, outside_nil, pfl_out, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by omega, by omega⟩, h1, ?_, ?_, ?_⟩ <;> omega

/-- the readiness of the runtime over every memory that frames the state (the five `H` hypotheses of `fast_arm64`), for the state with
memory `m`, local frame `r` (= `SP`), goroutine `g` and frame list `FRM` -/
def HypsH (H : RtReady) (rt : List (Nat × Nat)) (z : BitVec 64) (r g : Nat) (m : Memory) (FRM : List (Nat × Nat)) : Prop :=
  (∀ M, MemFrame m M FRM → 2 ^ 64 ≤ val256 m z.toNat →
      H [0, r - 384 + 94 + (98 - decLen (val256 m z.toNat)), decLen (val256 m z.toNat)] g (r - 384) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → 100 ≤ val256 m z.toNat → val256 m z.toNat < 2 ^ 64 →
      H [0, r - 384 - 32 + (24 - decLen (val256 m z.toNat)), decLen (val256 m z.toNat)] g (r - 384 - 96) (rtView rt M)) ∧
  (∀ M p l, MemFrame m M FRM → StrOut M p l (decBytes (val256 m z.toNat)) →
      DecAt rt 989280 1002589 960826 p l → H [0, p, l] g r (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → ∀ n, Fv256.C.hexDigits (val256 m z.toNat) n →
      H [0, r - 112 + 38 + (64 - n), n + 2] g (r - 112) (rtView rt M)) ∧
  (∀ M p l n, MemFrame m M FRM → Fv256.C.hexDigits (val256 m z.toNat) n →
      StrOut M p l (Fv256.C.hexStrBytes (val256 m z.toNat) n) → InRanges p l rt →
      H [0, p + 2, l - 2] g r (rtView rt M))

/-- the extra entry facts of the fast side (`z ≠ 0`) -/
def PreFastX (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧
  (s.regs 28).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4224 < s.sp.toNat ∧ Outside ((s.regs 28).toNat + 16) 8 rt ∧
  ((s.regs 28).toNat + 24 ≤ s.sp.toNat - 88 - stack ∨ s.sp.toNat + 40 ≤ (s.regs 28).toNat + 16) ∧
  HypsH H rt z (s.sp.toNat - 80) (s.regs 28).toNat s.mem (FLE rt s.sp.toNat stack)

theorem hypsH_of {H : RtReady} {rt : List (Nat × Nat)} {stack : Nat} {z : BitVec 64} {g r : Nat} {m m0 : Memory}
    (h8 : 88 + stack ≤ r) (hz : z.toNat + 32 ≤ r - 88 - stack ∨ r + 40 ≤ z.toNat)
    (hE : HypsH H rt z (r - 80) g m (FLE rt r stack)) (hfr : MemFrame m m0 (PFL r)) :
    HypsH H rt z (r - 80) g m0 (FL rt (r - 80) stack) := by
  have hzv : val256 m0 z.toNat = val256 m z.toNat := rdW (stack := stack) hfr hz
  have key : ∀ M, MemFrame m0 M (FL rt (r - 80) stack) → MemFrame m M (FLE rt r stack) := fun M hM =>
    hfr.trans hM (fun a n h => fle_sub h8 h)
  obtain ⟨e1, e2, e3, e4, e5⟩ := hE
  rw [HypsH]; rw [hzv]
  exact ⟨fun M hM => e1 M (key M hM), fun M hM => e2 M (key M hM), fun M p l hM => e3 M p l (key M hM),
    fun M hM => e4 M (key M hM), fun M p l n hM => e5 M p l n (key M hM)⟩

theorem dataLoaded_frame_w {p : Janus.Program} {m m' : Memory} (h : p.DataLoaded m) (hreg : m'.regions = m.regions)
    {a n : Nat} (hw : m.accessible a n true = true) (hfr : MemFrame m m' [(a, a + n)]) : p.DataLoaded m' := by
  intro d hd
  obtain ⟨hr, hb⟩ := h d hd
  have hap : a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a := dataLoaded_disjoint h hd hw
  refine ⟨by rw [hreg]; exact hr, fun i hi => ?_⟩
  have := hfr.readLE (d.base + i) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have h1 := Janus.Arm64.Memory.readLE_one m (d.base + i)
  have h2 := Janus.Arm64.Memory.readLE_one m' (d.base + i)
  rw [← hb i hi]
  omega

/-- the extra hypotheses of `fast_arm64`, at `S0` -/
theorem fx_of {H : RtReady} {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {fW fP fF fWr : Nat} {s S0 : State}
    (hc : PreCommon rt stack s) (hf : PreFastE rt stack z tab data fW fP fF fWr s) (hx : PreFastX H rt stack z s)
    (hsp : S0.sp = s.sp - 80#64) (h28 : S0.regs 28 = s.regs 28)
    (hfr : MemFrame s.mem S0.mem (PFL s.sp.toNat)) (hreg : S0.mem.regions = s.mem.regions) :
    Extracted.program.DataLoaded S0.mem ∧ GuardOK S0 4144 ∧
    Outside ((S0.regs 28).toNat + 16) 8 rt ∧
    ((S0.regs 28).toNat + 24 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ (S0.regs 28).toNat + 16) ∧
    HypsH H rt z S0.sp.toNat (S0.regs 28).toNat S0.mem (FL rt S0.sp.toNat stack) := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨c1, c2, c3, c4, t1, t2, t3, t4, t5, t6, t7, t8, z1, z2, z3⟩ := hf
  obtain ⟨xdl, xg1, xg2, xg3, xgo, xgd, xH⟩ := hx
  have hn : S0.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp, BitVec.toNat_sub]; have := s.sp.isLt; simp; omega
  refine ⟨dataLoaded_frame_w xdl hreg hacc ?_, ?_, ?_, ?_, ?_⟩
  · exact hfr.mono (fun a' n' h => by
      simp only [outside_cons, outside_nil, and_true] at h; rw [pfl_out]; omega)
  · unfold GuardOK; rw [h28]
    refine ⟨xg1, ?_, ?_⟩
    · rw [hfr.accessible]; exact xg2
    · rw [rdW (stack := stack) hfr (by omega), hn]; omega
  · rw [h28]; exact xgo
  · rw [h28, hn]; omega
  · rw [h28, hn]; exact hypsH_of hstk z3 xH hfr


/-- the entry-state memory frame of the nil path: `NilFL` at `S0` and the prefix frame -/
def NilFLE (R : IfaceModel) (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  NilFL R rt (r - 80) stack ++ PFL r

/-- the entry facts of the nil side (`z = 0`), the entry form of `NilPre` -/
def PreNilE (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab : BitVec 64) (s : State) : Prop :=
  CallerOK R s 80 40 ∧
  TADescOK R s.mem descA ∧ Outside descA 24 [(s.sp.toNat - 80 - R.depth, s.sp.toNat + 40)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ s.mem.accessible tab.toNat 0x14 false = true ∧ tyOf s tab ≠ 0 ∧ R.IsType (tyOf s tab) ∧
    (taCanFail s.mem descA = true ∨ (R.itab (taInter s.mem descA) (tyOf s tab)).isSome) ∧
    Outside (tab.toNat + 8) 8 (PFL s.sp.toNat)) ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside hdrA 16 (NilFLE R rt s.sp.toNat stack) ∧ Outside litA 5 (NilFLE R rt s.sp.toNat stack)

theorem callerOK_of {R : IfaceModel} (hl : R.Laws) {s S0 : State} (h : CallerOK R s 80 40)
    (hsp : S0.sp = s.sp - 80#64) (h28 : S0.regs 28 = s.regs 28) (hfr : MemFrame s.mem S0.mem (PFL s.sp.toNat)) :
    CallerOK R S0 0 0x78 := by
  obtain ⟨henv, hg, hal, hd, hdp, hb, hacc, hpriv, hdis, hgp⟩ := h
  have hn : S0.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp, BitVec.toNat_sub]; have := s.sp.isLt; simp; omega
  have hfr' : MemFrame s.mem S0.mem [(s.sp.toNat - (R.depth + 80), s.sp.toNat + 40)] :=
    hfr.mono (fun a n hh => by simp only [outside_cons, outside_nil, and_true] at hh; rw [pfl_out]; omega)
  have hag : Agrees s.mem S0.mem R.priv := Agrees.of_window hfr'
    (by rw [show s.sp.toNat + 40 - (s.sp.toNat - (R.depth + 80)) = R.depth + 80 + 40 by omega]; exact hpriv)
  simp only [Spec.Disjoint] at hdis
  have hgrd : S0.mem.readLE ((s.regs 28).toNat + 16) 8 = s.mem.readLE ((s.regs 28).toNat + 16) 8 :=
    hfr.readLE _ _ (by rw [pfl_out]; omega)
  have hsg : StackGuardOK S0 (R.depth + 0) := by
    obtain ⟨g1, g2, g3⟩ := hg
    refine ⟨by rw [h28]; exact g1, by rw [h28, hfr.accessible]; exact g2, ?_⟩
    simp only [stackguard0, regG, stackguard0Offset, h28, hgrd, hn] at g3 ⊢
    omega
  refine ⟨?_, hsg, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [h28]; exact hl.env_frame _ _ _ henv hag
  · rw [hn, show s.sp.toNat - 80 - (R.depth + 0) = s.sp.toNat - (R.depth + 80) by omega, hfr.accessible]
    rw [show R.depth + 0 + 0x78 = R.depth + 80 + 40 by omega]; exact hacc
  · rw [hn, show s.sp.toNat - 80 - (R.depth + 0) = s.sp.toNat - (R.depth + 80) by omega,
      show R.depth + 0 + 0x78 = R.depth + 80 + 40 by omega]; exact hpriv
  · rw [h28, hn]; simp only [Spec.Disjoint]; omega
  · rw [h28]; exact hgp


theorem strOut_frame {m m' : Memory} {ws : List (Nat × Nat)} {p n : Nat} {bs : List Nat} (hf : MemFrame m m' ws)
    (ho : Outside p n ws) (h : StrOut m p n bs) : StrOut m' p n bs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun hn => by rw [hf.accessible]; exact h3 hn, ?_⟩
  rw [← h4]
  apply Janus.Spec.strBytes_congr
  intro i hi
  have := hf.readLE (p + i) 1 (Outside.of_sub ho (by omega) (by omega))
  rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this

theorem nilpre_of {R : IfaceModel} (hl : R.Laws) {rt : List (Nat × Nat)} {stack : Nat} {tab data : BitVec 64} {s S0 : State}
    (hc : PreCommon rt stack s) (hn : PreNilE R rt stack tab s) (h8 : 8 ≤ stack)
    (hr0 : S0.regs 0 = 0#64) (hr1 : S0.regs 1 = tab) (hr2 : S0.regs 2 = data) (hsp : S0.sp = s.sp - 80#64)
    (h28 : S0.regs 28 = s.regs 28)
    (h104 : S0.mem.readLE (s.sp.toNat - 80 + 104) 8 = data.toNat)
    (hra : S0.mem.readLE (s.sp.toNat - 80) 8 = (s.regs 30).toNat) (hl4 : (s.regs 30).toNat % 4 = 0) (hl48 : (s.regs 30).toNat < 2 ^ 48)
    (hfr : MemFrame s.mem S0.mem (PFL s.sp.toNat)) : NilPre R rt stack tab data S0 := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨hco, hdesc, hdo, htab, qd, q4, q5⟩ := hn
  obtain ⟨q1, q2, q3⟩ := nil_rodata qd
  have hrn : S0.sp.toNat = s.sp.toNat - 80 := by
    rw [hsp, BitVec.toNat_sub]; have := s.sp.isLt; simp; omega
  have hco' := hco
  obtain ⟨-, -, -, hd8, -, -, -, hpriv, -, -⟩ := hco'
  have hws : ∀ a n, InRanges a n R.priv → Outside a n (PFL s.sp.toNat) := fun a n hin => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := MemFrame.outside_mem hpriv hr
    rw [pfl_out]; omega
  have hdo' : Outside descA 24 (PFL s.sp.toNat) := by
    simp only [outside_cons, outside_nil, and_true] at hdo; rw [pfl_out]; omega
  have hq4 : Outside hdrA 16 (NilFL R rt S0.sp.toNat stack) ∧ Outside hdrA 16 (PFL s.sp.toNat) := by
    simpa only [NilFLE, outside_append, hrn] using q4
  have hq5 : Outside litA 5 (NilFL R rt S0.sp.toNat stack) ∧ Outside litA 5 (PFL s.sp.toNat) := by
    simpa only [NilFLE, outside_append, hrn] using q5
  have hcall := callerOK_of hl hco hsp h28 hfr
  refine ⟨hr0, hr1, hr2, by omega, h8, by omega, by omega, ?_, ?_, ?_, ?_, ?_,
    hcall, TADescOK.frame hdesc hfr hdo' hws, ?_, ?_, ?_, ?_, ?_, hq4.1, hq5.1⟩
  · rw [hrn, show s.sp.toNat - 80 - stack = s.sp.toNat - 88 - stack + 8 by omega, hfr.accessible]
    exact Memory.accessible_mono _ hacc (by omega) (by omega)
  · rw [hrn, show s.sp.toNat - 80 - 8 - stack = s.sp.toNat - 88 - stack by omega]; exact hout
  · rw [hrn]; exact h104
  · rw [hrn, hra]; exact hl4
  · rw [hrn, hra]; exact hl48
  · rw [hrn, show s.sp.toNat - 80 + 0x78 = s.sp.toNat + 40 by omega]; exact hdo
  · intro htz
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := htab htz
    have hty : tyOf S0 tab = tyOf s tab := by
      unfold tyOf; exact hfr.readLE _ _ (by rw [pfl_out] at b6 ⊢; omega)
    have hcf := taCanFail_frame hfr hdo'
    have hin := taInter_frame hfr hdo'
    rw [hty, hcf, hin]
    exact ⟨b1, by rw [hfr.accessible]; exact b2, b3, b4, b5⟩
  · rw [hfr.readLE _ _ (Outside.of_sub hq4.2 (by omega) (by omega))]; exact q1
  · rw [hfr.readLE _ _ (Outside.of_sub hq4.2 (by omega) (by omega))]; exact q2
  · exact strOut_frame hfr hq5.2 q3


/-! ## The postconditions of the three cases, in terms of the entry state `s` and the final state `s'` -/

/-- nil receiver: one `fmt.Fprint(w, "<nil>")` -/
def NilPost (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (RFp : Res) (tab data : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (NilFLE R rt s.sp.toNat stack) ∧
  ∃ j0 j1 j2, RFp (BitVec.ofNat 64 (wOf R s tab)) data (BitVec.ofNat 64 (s.sp.toNat - 80 + 56)) 1#64 j0 j1 j2

/-- fast path: all queries answered plain, `ch ∈ {d, v, s, x}`, one `Write` -/
def FastPost (rt : List (Nat × Nat)) (stack fW fP fF : Nat) (RW RP RF RWr : Res) (data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (FL rt (s.sp.toNat - 80) stack ++ PFL s.sp.toNat) ∧
  (∃ ptr len cap j0 j1 j2, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j1 j2) ∧
  (∃ r3 j1, PlainHist RW RP RF data fW fP fF r3 j1) ∧
  (ch.toNat % 2 ^ 32 = 100 ∨ ch.toNat % 2 ^ 32 = 115 ∨ ch.toNat % 2 ^ 32 = 118 ∨ ch.toNat % 2 ^ 32 = 120)

/-- the frame of the big path, in entry terms: the allocator's ranges, the fast side's, the local slot `[S0.sp+8, S0.sp+56)` (arguments and the
`big.Int` slot) and the prefix's -/
def BigFL (R2 : RtInv) (rt : List (Nat × Nat)) (stack r : Nat) : List (Nat × Nat) :=
  R2.rt ++ FL rt (r - 80) stack ++ [(r - 72, r - 24)] ++ PFL r

/-- big path: some query answered "not plain" or `ch` not a fast verb, then one `(*big.Int).Format` call -/
def BigPost (R2 : RtInv) (rt : List (Nat × Nat)) (stack fW fP fF : Nat) (RW RP RF RBf : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (BigFL R2 rt stack s.sp.toNat) ∧
  NotPlain RW RP RF data fW fP fF ch (ch.toNat % 2 ^ 32) ∧
  ∃ P j0 j1 j2, RBf (BitVec.ofNat 64 P) tab data
    (BitVec.ofNat 64 (if ch.toNat % 2 ^ 32 < 2 ^ 31 then ch.toNat % 2 ^ 32 else ch.toNat % 2 ^ 32 + 18446744069414584320)) j0 j1 j2

theorem rtView_frame {rs : List (Nat × Nat)} {m m' : Memory} (hreg : m'.regions = m.regions)
    (hb : ∀ a, InRanges a 1 rs → m'.bytes a = m.bytes a) : rtView rs m' = rtView rs m := by
  unfold rtView
  congr 1
  · funext a
    by_cases h : rs.any (fun r => decide (r.1 ≤ a) && decide (a < r.2)) = true
    · rw [if_pos h, if_pos h]
      apply hb
      obtain ⟨r, hr, h2⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact ⟨r, hr, h2.1, by omega⟩
    · rw [if_neg h, if_neg h]

theorem view_frame {rs : List (Nat × Nat)} {m m' : Memory} {r stack : Nat} (hfr : MemFrame m m' (PFL r))
    (hreg : m'.regions = m.regions) (h8 : 88 + stack ≤ r)
    (hw : Outside (r - 88 - stack) (stack + 128) rs) : view rs [] m' = view rs [] m := by
  unfold view
  congr 1
  funext a
  by_cases hp : Outside a 1 (PFL r)
  · have := hfr.readLE a 1 hp
    rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
    rw [BitVec.eq_of_toNat_eq this]
  · have hin : r - 88 - stack ≤ a ∧ a < r - 88 - stack + (stack + 128) := by
      rw [pfl_out] at hp; omega
    rw [inRs_of_outside hw hin.1 hin.2]; simp

/-- layout facts about the callee-owned ranges `rt` (state-level, so the statement has no pure premise on `rt`) -/
def PreRt (rt : List (Nat × Nat)) : Prop :=
  (∀ r ∈ rt, 32 ≤ r.1) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) ∧
  Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 968614 256 rt

/-- the allocator facts of the big path (state-level: they mention the runtime model `R2`) -/
def PreBig (R2 : RtInv) (b0 : Nat) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Outside ((s.regs 28).toNat + 16) 8 R2.rt ∧ s.mem.accessible Fv256.Arm64.IntoBig.flagAddr 4 false = true ∧
  Outside Fv256.Arm64.IntoBig.bigType 16 R2.rt ∧ Outside Fv256.Arm64.IntoBig.arrType 16 R2.rt ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [Fv256.Arm64.IntoBig.bigType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.newobject") [Fv256.Arm64.IntoBig.arrType] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier1") [1] ∧
  R2.ok (Extracted.program.contractAddr "runtime.gcWriteBarrier2") [2] ∧
  blockSize 32 false + blockSize 32 true ≤ b0 ∧
  Outside (s.sp.toNat - 88 - stack) (stack + 128) R2.rt ∧ Outside z.toNat 32 R2.rt

/-- the assembly precondition, at the entry state `s` -/
def PreF (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat)) (stack b0 fW fP fF fWr zv : Nat)
    (z tab data : BitVec 64) (s : State) : Prop :=
  PreRt rt ∧ PreCommon rt stack s ∧
  (z.toNat = 0 → PreNilE R rt stack tab s ∧
    (tab.toNat ≠ 0 → H [descA, tyOf s tab] (s.regs 28).toNat (s.sp.toNat - 80) (rtView R.priv s.mem))) ∧
  (z.toNat ≠ 0 → PreFastE rt stack z tab data fW fP fF fWr s ∧ PreFastX H rt stack z s ∧
    val256 s.mem z.toNat = zv ∧ R2.inv b0 [] (s.regs 28).toNat (view R2.rt [] s.mem) ∧ PreBig R2 b0 rt stack z s)

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]

theorem sp0_toNat {s S0 : State} (hc : 80 ≤ s.sp.toNat) (hsp : S0.sp = s.sp - 80#64) :
    S0.sp.toNat = s.sp.toNat - 80 := by
  rw [hsp, BitVec.toNat_sub]; have := s.sp.isLt; simp; omega

/-- the ABI obligations on return, from the exit facts of the paths -/
theorem abi_of {s S0 S' : State} (hc : 88 ≤ s.sp.toNat) (hsp : S0.sp = s.sp - 80#64)
    (hrfp : S0.mem.readLE (s.sp.toNat - 88) 8 = (s.regs 29).toNat) (h28 : S0.regs 28 = s.regs 28) (h18 : S0.regs 18 = s.regs 18)
    (e4 : S'.sp = S0.sp + 80#64)
    (e29 : S'.regs 29 = BitVec.ofNat 64 (S0.mem.readLE (S0.sp.toNat - 8) 8))
    (e28 : S'.regs 28 = S0.regs 28) (e18 : S'.regs 18 = S0.regs 18) : ABIReturn s S' := by
  have hn := sp0_toNat (s := s) (by omega) hsp
  refine ⟨?_, ?_, ?_, ?_⟩
  · show S'.sp = s.sp
    rw [e4, hsp]; bv_omega
  · show S'.regs 28 = s.regs 28
    rw [e28, h28]
  · show S'.regs 29 = s.regs 29
    rw [e29, hn, show s.sp.toNat - 80 - 8 = s.sp.toNat - 88 by omega, hrfp, ofNat_toNat64]
  · show S'.regs 18 = s.regs 18
    rw [e18, h18]

theorem priv_out {R : IfaceModel} {s : State} (hco : CallerOK R s 80 40) :
    ∀ a n, InRanges a n R.priv → Outside a n (PFL s.sp.toNat) := by
  obtain ⟨-, -, -, hd8, -, -, -, hpriv, -, -⟩ := hco
  intro a n hin
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem hpriv hr
  rw [pfl_out]; omega

theorem wOf_frame {R : IfaceModel} {s S0 : State} {tab : BitVec 64} (hfr : MemFrame s.mem S0.mem (PFL s.sp.toNat))
    (hd : Outside descA 24 (PFL s.sp.toNat)) (ht : tab.toNat ≠ 0 → Outside (tab.toNat + 8) 8 (PFL s.sp.toNat)) :
    wOf R S0 tab = wOf R s tab := by
  unfold wOf
  by_cases h : tab.toNat = 0
  · simp [h]
  · simp only [h, if_false]
    have e1 : tyOf S0 tab = tyOf s tab := by unfold tyOf; exact hfr.readLE _ _ (ht h)
    rw [e1, taInter_frame hfr hd]

theorem bytes_frame {m m' : Memory} {ws : List (Nat × Nat)} {a : Nat} (hf : MemFrame m m' ws) (h : Outside a 1 ws) :
    m'.bytes a = m.bytes a := by
  have := hf.readLE a 1 h
  rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
  exact BitVec.eq_of_toNat_eq this


theorem bigfl_sub {R2 : RtInv} {rt : List (Nat × Nat)} {stack r a n : Nat} (h8 : 88 + stack ≤ r) (h : Outside a n (BigFL R2 rt stack r)) :
    Outside a n (PFL r) ∧ Outside a n (FL rt (r - 80) stack) ∧
    Outside a n (R2.rt ++ rt ++ [(r - 80 - stack, r - 88), (r - 72, r - 24)]) := by
  simp only [BigFL, FL, outside_append, outside_cons, outside_nil, pfl_out, and_true] at h ⊢
  obtain ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7, h8'⟩ := h
  refine ⟨⟨h7, h8'⟩, ⟨h2, ?_, ?_, ?_⟩, ⟨⟨h1, h2⟩, ?_, ?_⟩⟩ <;> omega

end Fv256.Arm64.FormatTransfer
