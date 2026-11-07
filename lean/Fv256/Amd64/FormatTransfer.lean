import Extracted
import Fv256.FormatFastDefs
import Fv256.Amd64.FormatNil
import Fv256.Amd64.FormatNilRodata
import Fv256.Amd64.FormatBigDefs
import Fv256.DecAt
import Fv256.IntoBigCommon
import Fv256.Amd64.FormatFastPre
import Fv256.SpecC
import Fv256.SpecE

/-!
# `Format` (amd64): the assembly precondition `PreF` and the transfer lemmas across the prefix

`PreF` is stated at the ENTRY state `s`.  The prefix (`FormatPrefix.prefix_nz` / `prefix_z`) runs to `S0` (entry `RSP` - 72) and changes memory
only inside `PFL (RSP)` = `[RSP-80, RSP)` and `[RSP+16, RSP+32)`.  Every memory fact of `FPre` / `NilPre` at `S0` is moved back to `s`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Janus.Contracts.IfaceAmd64
  Janus.Spec Janus.Spec.Type Janus.Spec.Map
open Fv256.FormatFast Fv256.Amd64.FormatNil Fv256.E

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace Fv256.Amd64.FormatTransfer

/-- the memory the prefix writes (`r` = the entry `RSP`): the frame `[r-80, r)` and the argument spill slots `[r+16, r+32)` -/
def PFL (r : Nat) : List (Nat × Nat) := [(r - 80, r), (r + 16, r + 32)]

theorem pfl_out {r a n : Nat} : Outside a n (PFL r) ↔ ((a + n ≤ r - 80 ∨ r ≤ a) ∧ (a + n ≤ r + 16 ∨ r + 32 ≤ a)) := by
  simp [PFL]

/-- a range outside the window `[r-80-stack, r+48)` is untouched by the prefix -/
theorem rdW {m m' : Memory} {r stack a n : Nat} (hf : MemFrame m m' (PFL r)) (h : a + n ≤ r - 80 - stack ∨ r + 48 ≤ a) :
    m'.readLE a n = m.readLE a n :=
  hf.readLE a n (by rw [pfl_out]; omega)

theorem outW {r stack a n : Nat} (h : a + n ≤ r - 80 - stack ∨ r + 48 ≤ a) : Outside a n (PFL r) := by
  rw [pfl_out]; omega

/-- the common call facts (the hypotheses of `prefix_nz` / `prefix_z`) -/
def PreCommon (rt : List (Nat × Nat)) (stack : Nat) (s : State) : Prop :=
  StackGuardOK s 0 ∧ (s.regs 4).toNat % 8 = 0 ∧ 80 + stack ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 48 ≤ 2 ^ 48 ∧
  s.mem.accessible ((s.regs 4).toNat - 80 - stack) (stack + 0x80) true = true ∧
  Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) rt

/-- the entry facts of the fast / big side (`z ≠ 0`), the entry-state form of `FPre` and the extra hypotheses of `fast_amd64` -/
def PreFastE (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (s : State) : Prop :=
  CodePtrOK64 fW ∧ CodePtrOK64 fP ∧ CodePtrOK64 fF ∧ CodePtrOK64 fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ s.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  s.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ s.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  s.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ s.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x18 + 32 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ tab.toNat + 0x18) ∧
  z.toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible z.toNat 32 false = true ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ z.toNat)

/-- `FPre` at `S0` from the entry facts -/
theorem fpre_of {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {fW fP fF fWr : Nat} {s S0 : State}
    (hc : PreCommon rt stack s) (hf : PreFastE rt stack z tab data fW fP fF fWr s)
    (hr0 : S0.regs 0 = z) (hr3 : S0.regs 3 = tab) (hr1 : S0.regs 1 = data) (hr4 : S0.regs 4 = s.regs 4 - 72#64)
    (hr5 : S0.regs 5 = s.regs 4 - 8#64)
    (h58 : S0.mem.readLE ((s.regs 4).toNat - 72 + 0x58) 8 = tab.toNat) (h60 : S0.mem.readLE ((s.regs 4).toNat - 72 + 0x60) 8 = data.toNat)
    (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat)) : FPre rt stack z tab data fW fP fF fWr S0 := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨c1, c2, c3, c4, t1, t2, t3, t4, t5, t6, t7, t8, z1, z2, z3, z4⟩ := hf
  have hrsp : S0.regs 4 = s.regs 4 - 72#64 := hr4
  have hn : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hrsp, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega
  have hn5 : S0.regs 5 = S0.regs 4 + 64#64 := by
    rw [hr5, hrsp]; bv_omega
  refine ⟨hr0, hr3, hr1, hn5, by omega, by omega, by omega, ?_, ?_, ?_, ?_, c1, c2, c3, c4, t1, ?_, ?_, ?_, ?_, ?_, t7, ?_, z1, ?_, z3, ?_⟩
  · rw [hn, show (s.regs 4).toNat - 72 - 8 - stack = (s.regs 4).toNat - 80 - stack by omega, hfr.accessible]; exact hacc
  · rw [hn, show (s.regs 4).toNat - 72 - 8 - stack = (s.regs 4).toNat - 80 - stack by omega]; exact hout
  · rw [hn]; exact h58
  · rw [hn]; exact h60
  · rw [hfr.accessible]; exact t2
  · rw [rdW (stack := stack) hfr (by omega)]; exact t3
  · rw [rdW (stack := stack) hfr (by omega)]; exact t4
  · rw [rdW (stack := stack) hfr (by omega)]; exact t5
  · rw [rdW (stack := stack) hfr (by omega)]; exact t6
  · rw [hn]; omega
  · rw [hfr.accessible]; exact z2
  · rw [hn]; omega


/-- the window-wide frame of the fast side, in entry terms: `rt` and the whole window `[r-80-stack, r+48)` -/
def FLE (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) := rt ++ [(r - 80 - stack, r + 48)]

theorem fle_sub {rt : List (Nat × Nat)} {r stack : Nat} (h8 : 80 + stack ≤ r) {a n : Nat} (h : Outside a n (FLE rt r stack)) :
    Outside a n (PFL r) ∧ Outside a n (FL rt (r - 72) stack) := by
  simp only [FLE, FL, outside_append, outside_cons, outside_nil, pfl_out, and_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by omega, by omega⟩, h1, ?_, ?_⟩ <;> omega

/-- the readiness of the runtime over every memory that frames the state (the five `H` hypotheses of `fast_amd64`), for the state with
memory `m`, local frame `r` (= `RSP`), goroutine `g` and frame list `FRM` -/
def HypsH (H : RtReady) (rt : List (Nat × Nat)) (z : BitVec 64) (r g : Nat) (m : Memory) (FRM : List (Nat × Nat)) : Prop :=
  (∀ M, MemFrame m M FRM → 2 ^ 64 ≤ m.readLE z.toNat 32 →
      H [0, r - 8 - 0x178 + 86 + (98 - decLen (m.readLE z.toNat 32)), decLen (m.readLE z.toNat 32)] g (r - 8 - 0x178 - 8) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → 100 ≤ m.readLE z.toNat 32 → m.readLE z.toNat 32 < 2 ^ 64 →
      H [0, r - 8 - 384 - 0x20 + (24 - decLen (m.readLE z.toNat 32)), decLen (m.readLE z.toNat 32)] g (r - 8 - 384 - 0x58) (rtView rt M)) ∧
  (∀ M p l, MemFrame m M FRM → StrOut M p l (decBytes (m.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l → H [0, p, l] g (r - 8) (rtView rt M)) ∧
  (∀ M, MemFrame m M FRM → ∀ n, Fv256.C.hexDigits (m.readLE z.toNat 32) n →
      H [0, r - 8 - 112 + 38 + (64 - n), n + 2] g (r - 8 - 112) (rtView rt M)) ∧
  (∀ M p l n, MemFrame m M FRM → Fv256.C.hexDigits (m.readLE z.toNat 32) n →
      StrOut M p l (Fv256.C.hexStrBytes (m.readLE z.toNat 32) n) → InRanges p l rt →
      H [0, p + 2, l - 2] g (r - 8) (rtView rt M))

/-- the extra entry facts of the fast side (`z ≠ 0`) -/
def PreFastX (H : RtReady) (rt : List (Nat × Nat)) (stack : Nat) (z : BitVec 64) (s : State) : Prop :=
  Extracted.program.DataLoaded s.mem ∧
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 14).toNat + 16) 8 + 0x378 < (s.regs 4).toNat - 80 ∧ Outside ((s.regs 14).toNat + 16) 8 rt ∧
  ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ (s.regs 14).toNat + 16) ∧
  HypsH H rt z ((s.regs 4).toNat - 72) (s.regs 14).toNat s.mem (FLE rt (s.regs 4).toNat stack)

theorem hypsH_of {H : RtReady} {rt : List (Nat × Nat)} {stack : Nat} {z : BitVec 64} {g rsp : Nat} {m m0 : Memory}
    (h8 : 80 + stack ≤ rsp) (hz : z.toNat + 32 ≤ rsp - 80 - stack ∨ rsp + 48 ≤ z.toNat)
    (hE : HypsH H rt z (rsp - 72) g m (FLE rt rsp stack)) (hfr : MemFrame m m0 (PFL rsp)) :
    HypsH H rt z (rsp - 72) g m0 (FL rt (rsp - 72) stack) := by
  have hzv : m0.readLE z.toNat 32 = m.readLE z.toNat 32 := rdW (stack := stack) hfr hz
  have key : ∀ M, MemFrame m0 M (FL rt (rsp - 72) stack) → MemFrame m M (FLE rt rsp stack) := fun M hM =>
    hfr.trans hM (fun a n h => fle_sub h8 h)
  obtain ⟨e1, e2, e3, e4, e5⟩ := hE
  rw [HypsH]; rw [hzv]
  exact ⟨fun M hM => e1 M (key M hM), fun M hM => e2 M (key M hM), fun M p l hM => e3 M p l (key M hM),
    fun M hM => e4 M (key M hM), fun M p l n hM => e5 M p l n (key M hM)⟩

theorem dataLoaded_frame {p : Janus.Amd64.Program} {m m' : Memory} (h : p.DataLoaded m) (hreg : m'.regions = m.regions)
    {a n : Nat} (hw : m.accessible a n true = true) (hfr : MemFrame m m' [(a, a + n)]) : p.DataLoaded m' := by
  intro d hd
  obtain ⟨hr, hb⟩ := h d hd
  have hap : a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a := by
    have hk := List.mem_iff_getElem.1 hd
    obtain ⟨k, hk, rfl⟩ := hk
    exact disjoint_of_dataLoaded h k hk hw
  refine ⟨by rw [hreg]; exact hr, fun i hi => ?_⟩
  have := hfr.readLE (d.base + i) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)
  have h1 := Janus.Arm64.Memory.readLE_one m (d.base + i)
  have h2 := Janus.Arm64.Memory.readLE_one m' (d.base + i)
  rw [← hb i hi]
  omega

/-- `DataLoaded` survives a run whose memory changes only in `FL rt r stack` (data objects are outside `rt` and read-only) -/
theorem dataLoaded_FL {m m' : Memory} {rt : List (Nat × Nat)} {r stack : Nat} (h : Extracted.program.DataLoaded m)
    (hreg : m'.regions = m.regions) (hdrt : ∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt)
    (hw : m.accessible (r - 8 - stack) (stack + 0x80) true = true) (hf : MemFrame m m' (FL rt r stack)) :
    Extracted.program.DataLoaded m' := by
  intro d hd
  obtain ⟨hr, hb⟩ := h d hd
  have hap : ∀ a n, (r - 8 - stack ≤ a ∧ a + n ≤ r - 8 - stack + (stack + 0x80)) → (a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a) := by
    intro a n han
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hd
    exact disjoint_of_dataLoaded h k hk (Janus.Arm64.Memory.accessible_mono m hw han.1 (by omega))
  refine ⟨by rw [hreg]; exact hr, fun i hi => ?_⟩
  have h1 := hap (r - 8 - stack) (stack + 40) ⟨Nat.le_refl _, by omega⟩
  have h2 := hap (r + 0x50) 28 ⟨by omega, by omega⟩
  have hdr := hdrt d hd
  have := hf.readLE (d.base + i) 1 (by
    simp only [FL, outside_append, outside_cons, outside_nil, and_true] at hdr ⊢
    refine ⟨Outside.of_sub hdr (by omega) (by omega), ?_, ?_⟩ <;> omega)
  have h1' := Janus.Arm64.Memory.readLE_one m (d.base + i)
  have h2' := Janus.Arm64.Memory.readLE_one m' (d.base + i)
  rw [← hb i hi]
  omega

/-- the extra hypotheses of `fast_amd64`, at `S0` -/
theorem fx_of {H : RtReady} {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {s S0 : State}
    (hc : PreCommon rt stack s) (hf : PreFastE rt stack z tab data fW fP fF fWr s) (hx : PreFastX H rt stack z s)
    (hr4 : S0.regs 4 = s.regs 4 - 72#64) (hr14 : S0.regs 14 = s.regs 14)
    (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat)) (hreg : S0.mem.regions = s.mem.regions) :
    Extracted.program.DataLoaded S0.mem ∧
    (S0.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true ∧
    S0.mem.readLE ((S0.regs 14).toNat + 16) 8 + 0x378 < (S0.regs 4).toNat - 8 ∧ Outside ((S0.regs 14).toNat + 16) 8 rt ∧
    ((S0.regs 14).toNat + 24 ≤ (S0.regs 4).toNat - 8 - stack ∨ (S0.regs 4).toNat + 0x78 ≤ (S0.regs 14).toNat + 16) ∧
    HypsH H rt z (S0.regs 4).toNat (S0.regs 14).toNat S0.mem (FL rt (S0.regs 4).toNat stack) := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨c1, c2, c3, c4, t1, t2, t3, t4, t5, t6, t7, t8, z1, z2, z3, z4⟩ := hf
  obtain ⟨xdl, xg1, xg2, xg3, xgo, xgd, xH⟩ := hx
  have hn : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega
  rw [hr14]
  refine ⟨dataLoaded_frame xdl hreg hacc ?_, xg1, ?_, ?_, xgo, ?_, ?_⟩
  · exact hfr.mono (fun a' n' h => by
      simp only [outside_cons, outside_nil, and_true] at h; rw [pfl_out]; omega)
  · rw [hfr.accessible]; exact xg2
  · rw [rdW (stack := stack) hfr (by omega), hn]; omega
  · rw [hn]; omega
  · rw [hn]; exact hypsH_of hstk z4 xH hfr


/-- the entry-state memory frame of the nil path: `NilFL` at `S0` and the prefix frame -/
def NilFLE (R : IfaceModel) (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  NilFL R rt (r - 72) stack ++ PFL r

/-- the entry facts of the nil side (`z = 0`), the entry form of `NilPre` -/
def PreNilE (R : IfaceModel) (rt : List (Nat × Nat)) (stack : Nat) (tab : BitVec 64) (s : State) : Prop :=
  CallerOK R s 80 48 ∧
  TADescOK R s.mem descA ∧ Outside descA 24 [((s.regs 4).toNat - 80 - R.depth, (s.regs 4).toNat + 48)] ∧
  (tab.toNat ≠ 0 →
    tab.toNat + 0x14 ≤ 2 ^ 48 ∧ s.mem.accessible tab.toNat 0x14 false = true ∧ tyOf s tab ≠ 0 ∧ R.IsType (tyOf s tab) ∧
    (taCanFail s.mem descA = true ∨ (R.itab (taInter s.mem descA) (tyOf s tab)).isSome) ∧
    Outside (tab.toNat + 8) 8 (PFL (s.regs 4).toNat)) ∧
  Extracted.program.DataLoaded s.mem ∧
  Outside hdrA 16 (NilFLE R rt (s.regs 4).toNat stack) ∧ Outside litA 5 (NilFLE R rt (s.regs 4).toNat stack)

theorem callerOK_of {R : IfaceModel} (hl : R.Laws) {s S0 : State} (h : CallerOK R s 80 48)
    (hr4 : S0.regs 4 = s.regs 4 - 72#64) (hr14 : S0.regs 14 = s.regs 14) (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat)) :
    CallerOK R S0 8 0x78 := by
  obtain ⟨henv, hg, hal, hd, hb, hacc, hpriv, hdis, hgp⟩ := h
  have hn : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega
  have hw : (s.regs 4).toNat - (R.depth + 80) + (R.depth + 80 + 48) = (s.regs 4).toNat + 48 := by omega
  have hfr' : MemFrame s.mem S0.mem [((s.regs 4).toNat - (R.depth + 80), (s.regs 4).toNat + 48)] :=
    hfr.mono (fun a n hh => by simp only [outside_cons, outside_nil, and_true] at hh; rw [pfl_out]; omega)
  have hag : Agrees s.mem S0.mem R.priv := Agrees.of_window hfr' (by rw [show (s.regs 4).toNat + 48 - ((s.regs 4).toNat - (R.depth + 80)) = R.depth + 80 + 48 by omega]; exact hpriv)
  simp only [Spec.Disjoint] at hdis
  have hgrd : S0.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hfr.readLE _ _ (by rw [pfl_out]; omega)
  have hsg : StackGuardOK S0 (R.depth + 8) := by
    obtain ⟨g1, g2, g3⟩ := hg
    refine ⟨by rw [hr14]; exact g1, by rw [hr14, hfr.accessible]; exact g2, ?_⟩
    simp only [stackguard0, regG, stackguard0Offset, regSP, hr14, hgrd] at g3 ⊢
    omega
  refine ⟨?_, hsg, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [hr14]; exact hl.env_frame _ _ _ henv hag
  · rw [hn, show (s.regs 4).toNat - 72 - (R.depth + 8) = (s.regs 4).toNat - (R.depth + 80) by omega, hfr.accessible]; exact hacc
  · rw [hn, show (s.regs 4).toNat - 72 - (R.depth + 8) = (s.regs 4).toNat - (R.depth + 80) by omega]; exact hpriv
  · rw [hn, hr14, show (s.regs 4).toNat - 72 - (R.depth + 8) = (s.regs 4).toNat - (R.depth + 80) by omega]; simp only [Spec.Disjoint]; omega
  · rw [hr14]; exact hgp

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
    (hc : PreCommon rt stack s) (hn : PreNilE R rt stack tab s)
    (hr0 : S0.regs 0 = 0#64) (hr3 : S0.regs 3 = tab) (hr1 : S0.regs 1 = data) (hr4 : S0.regs 4 = s.regs 4 - 72#64)
    (hr5 : S0.regs 5 = s.regs 4 - 8#64) (hr14 : S0.regs 14 = s.regs 14) (hx : S0.xmm = s.xmm) (hdf : S0.df = s.df)
    (hx0 : s.xmm 15 = 0) (hdf0 : s.df = false) (hret : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47)
    (h60 : S0.mem.readLE ((s.regs 4).toNat - 72 + 0x60) 8 = data.toNat)
    (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat)) : NilPre R rt stack tab data S0 := by
  obtain ⟨-, hal, hstk, hhi, hacc, hout⟩ := hc
  obtain ⟨hco, hdesc, hdo, htab, qd, q4, q5⟩ := hn
  obtain ⟨q1, q2, q3⟩ := nil_rodata qd
  have hrn : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega
  have hn5 : S0.regs 5 = S0.regs 4 + 64#64 := by
    rw [hr5, hr4]; bv_omega
  have hco' := hco
  obtain ⟨-, -, -, -, -, -, hpriv, -, -⟩ := hco'
  have hws : ∀ a n, InRanges a n R.priv → Outside a n (PFL (s.regs 4).toNat) := fun a n hin => by
    obtain ⟨r, hr, h1, h2⟩ := hin
    have := MemFrame.outside_mem hpriv hr
    rw [pfl_out]; omega
  have hdo' : Outside descA 24 (PFL (s.regs 4).toNat) := by
    simp only [outside_cons, outside_nil, and_true] at hdo; rw [pfl_out]; omega
  have hq4 : Outside hdrA 16 (NilFL R rt (S0.regs 4).toNat stack) ∧ Outside hdrA 16 (PFL (s.regs 4).toNat) := by
    simpa only [NilFLE, outside_append, hrn] using q4
  have hq5 : Outside litA 5 (NilFL R rt (S0.regs 4).toNat stack) ∧ Outside litA 5 (PFL (s.regs 4).toNat) := by
    simpa only [NilFLE, outside_append, hrn] using q5
  have hcall := callerOK_of hl hco hr4 hr14 hfr
  refine ⟨hr0, hr3, hr1, hn5, by omega, by omega, by omega, ?_, ?_, ?_, ?_, by rw [hx]; exact hx0, by rw [hdf]; exact hdf0,
    hcall, TADescOK.frame hdesc hfr hdo' hws, ?_, ?_, ?_, ?_, ?_, hq4.1, hq5.1⟩
  · rw [hrn, show (s.regs 4).toNat - 72 - 8 - stack = (s.regs 4).toNat - 80 - stack by omega, hfr.accessible]; exact hacc
  · rw [hrn, show (s.regs 4).toNat - 72 - 8 - stack = (s.regs 4).toNat - 80 - stack by omega]; exact hout
  · rw [hrn]; exact h60
  · rw [hrn, show (s.regs 4).toNat - 72 + 0x48 = (s.regs 4).toNat by omega, hfr.readLE _ _ (by rw [pfl_out]; omega)]; exact hret
  · rw [hrn, show (s.regs 4).toNat - 72 - 8 - R.depth = (s.regs 4).toNat - 80 - R.depth by omega,
      show (s.regs 4).toNat - 72 + 0x78 = (s.regs 4).toNat + 48 by omega]; exact hdo
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
  MemFrame s.mem s'.mem (NilFLE R rt (s.regs 4).toNat stack) ∧
  ∃ j0 j3 j1, RFp (BitVec.ofNat 64 (wOf R s tab)) data (BitVec.ofNat 64 ((s.regs 4).toNat - 72 + 0x30)) 1#64 j0 j3 j1

/-- fast path: all queries answered plain, `ch ∈ {d, v, s, x}`, one `Write` -/
def FastPost (rt : List (Nat × Nat)) (stack fP fF : Nat) (RW RP RF RWr : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (FL rt ((s.regs 4).toNat - 72) stack ++ PFL (s.regs 4).toNat) ∧
  (∃ ptr len cap j0 j3 j1, RWr data (BitVec.ofNat 64 ptr) (BitVec.ofNat 64 len) (BitVec.ofNat 64 cap) j0 j3 j1) ∧
  (∃ j3, PlainHist RW RP RF data tab ch j3 fP fF) ∧
  (ch.toNat % 2 ^ 32 = 100 ∨ ch.toNat % 2 ^ 32 = 115 ∨ ch.toNat % 2 ^ 32 = 118 ∨ ch.toNat % 2 ^ 32 = 120)

/-- big path: some query answered "not plain" or `ch` not a fast verb, then one `(*big.Int).Format` call -/
def BigPost (R2 : RtInv) (rt : List (Nat × Nat)) (stack fP fF : Nat) (RW RP RF RBf : Res) (tab data ch : BitVec 64) (s s' : State) : Prop :=
  MemFrame s.mem s'.mem (R2.rt ++ FL rt ((s.regs 4).toNat - 72) stack ++ [((s.regs 4).toNat - 72 + 0x28, (s.regs 4).toNat - 72 + 0x30)] ++ PFL (s.regs 4).toNat) ∧
  Fv256.Amd64.FormatFast.NotPlain RW RP RF data tab ch fP fF (ch.toNat % 2 ^ 32) ∧
  ∃ P j0 j3 j1, RBf (BitVec.ofNat 64 P) tab data (BitVec.ofNat 64 (ch.toNat % 2 ^ 32)) j0 j3 j1

/-- the state-level result of the big path from the `Format+0x1cc` state (the interface of the big-path lemma (iii)) -/
abbrev BigQ := @Fv256.Amd64.FormatBig.BigQ

/-- the allocator invariant survives any callee: memory changed only inside `rt` and the callee windows keeps `R2.inv`
(the named assumption `CalleePreservesRt R2`: well-behaved Go code keeps the runtime's invariant) -/
def CalleePreservesRt (R2 : RtInv) (rt : List (Nat × Nat)) (stack : Nat) : Prop :=
  ∀ (S0 S : State) (b : Nat), MemFrame S0.mem S.mem (FL rt (S0.regs 4).toNat stack) → S.regs 14 = S0.regs 14 →
    R2.inv b [] (S0.regs 14).toNat (view R2.rt [] S0.mem) → R2.inv b [] (S.regs 14).toNat (view R2.rt [] S.mem)


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
    (hreg : m'.regions = m.regions) (h8 : 80 + stack ≤ r)
    (hw : Outside (r - 80 - stack) (stack + 0x80) rs) : view rs [] m' = view rs [] m := by
  unfold view
  congr 1
  funext a
  by_cases hp : Outside a 1 (PFL r)
  · have := hfr.readLE a 1 hp
    rw [Janus.Arm64.Memory.readLE_one, Janus.Arm64.Memory.readLE_one] at this
    rw [BitVec.eq_of_toNat_eq this]
  · have hin : r - 80 - stack ≤ a ∧ a < r - 80 - stack + (stack + 0x80) := by
      rw [pfl_out] at hp; omega
    rw [inRs_of_outside hw hin.1 hin.2]; simp

/-- layout facts about the callee-owned ranges `rt` (state-level, so the statement has no pure premise on `rt`) -/
def PreRt (rt : List (Nat × Nat)) : Prop :=
  (∀ r ∈ rt, 32 ≤ r.1) ∧ (∀ d ∈ Extracted.program.data, Outside d.base d.bytes.length rt) ∧
  Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ Outside 5142664 256 rt

/-- the assembly precondition, at the entry state `s` -/
def PreF (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat)) (stack b0 : Nat) (fW fP fF fWr zv : Nat)
    (z tab data : BitVec 64) (s : State) : Prop :=
  PreRt rt ∧ PreCommon rt stack s ∧
  (z.toNat = 0 → PreNilE R rt stack tab s ∧
    (tab.toNat ≠ 0 → H [descA, tyOf s tab] (s.regs 14).toNat ((s.regs 4).toNat - 80) (rtView R.priv s.mem))) ∧
  (z.toNat ≠ 0 → PreFastE rt stack z tab data fW fP fF fWr s ∧ PreFastX H rt stack z s ∧
    s.mem.readLE z.toNat 32 = zv ∧ R2.inv b0 [] (s.regs 14).toNat (view R2.rt [] s.mem) ∧
    Outside ((s.regs 4).toNat - 80 - stack) (stack + 0x80) R2.rt ∧ Fv256.Amd64.FormatBig.PreBigE R2 b0 z s)

theorem bigR2_of {R2 : RtInv} {b0 : Nat} {z : BitVec 64} {s S0 : State} {stack : Nat}
    (hb : Fv256.Amd64.FormatBig.PreBigE R2 b0 z s) (hstk : 80 + stack ≤ (s.regs 4).toNat)
    (hr4 : S0.regs 4 = s.regs 4 - 72#64) (hr14 : S0.regs 14 = s.regs 14) (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat))
    (hgd : (s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 80 - stack ∨ (s.regs 4).toNat + 48 ≤ (s.regs 14).toNat + 16) :
    Fv256.Amd64.FormatBig.BigR2 R2 b0 z S0 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  have hn : (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [hr4, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega
  rw [Fv256.Amd64.FormatBig.BigR2, hr14, hn, rdW (stack := stack) hfr (by omega), hfr.accessible]
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩


theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt x.isLt]

theorem rsp0_toNat {s S0 : State} (hc : 80 ≤ (s.regs 4).toNat) (hr4 : S0.regs 4 = s.regs 4 - 72#64) :
    (S0.regs 4).toNat = (s.regs 4).toNat - 72 := by
  rw [hr4, BitVec.toNat_sub]; have := (s.regs 4).isLt; simp; omega

/-- the ABI obligations on return, from the exit facts of the paths -/
theorem abi_of {s S0 S' : State} (hc : 80 ≤ (s.regs 4).toNat) (hr4 : S0.regs 4 = s.regs 4 - 72#64)
    (hrbp : S0.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) (hr14 : S0.regs 14 = s.regs 14)
    (hxmm : S0.xmm = s.xmm)
    (e4 : S'.regs 4 = S0.regs 4 + 80#64)
    (e5 : S'.regs 5 = BitVec.ofNat 64 (S0.mem.readLE ((S0.regs 4).toNat + 64) 8))
    (e14 : S'.regs 14 = S0.regs 14) (ex : S'.xmm 15 = S0.xmm 15) : ABIReturn s S' := by
  have hn := rsp0_toNat hc hr4
  refine ⟨?_, ?_, ?_, ?_⟩
  · show S'.regs 4 = s.regs 4 + 8#64
    rw [e4, hr4]; bv_omega
  · show S'.regs 5 = s.regs 5
    rw [e5, hn, show (s.regs 4).toNat - 72 + 64 = (s.regs 4).toNat - 8 by omega, hrbp, ofNat_toNat64]
  · show S'.regs 14 = s.regs 14
    rw [e14, hr14]
  · show S'.xmm 15 = s.xmm 15
    rw [ex, hxmm]

theorem priv_out {R : IfaceModel} {s : State} (hco : CallerOK R s 80 48) :
    ∀ a n, InRanges a n R.priv → Outside a n (PFL (s.regs 4).toNat) := by
  obtain ⟨-, -, -, -, -, -, hpriv, -, -⟩ := hco
  intro a n hin
  obtain ⟨r, hr, h1, h2⟩ := hin
  have := MemFrame.outside_mem hpriv hr
  rw [pfl_out]; omega

theorem wOf_frame {R : IfaceModel} {s S0 : State} {tab : BitVec 64} (hfr : MemFrame s.mem S0.mem (PFL (s.regs 4).toNat))
    (hd : Outside descA 24 (PFL (s.regs 4).toNat)) (ht : tab.toNat ≠ 0 → Outside (tab.toNat + 8) 8 (PFL (s.regs 4).toNat)) :
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

end Fv256.Amd64.FormatTransfer
