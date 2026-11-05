import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.SetFromHexLoops

/-!
# `(*uint256.Int).SetFromHex(hex string) error` (arm64)

The wrapper around the non-inlined `fromHex`; the parse itself is the callee summary `SetFromHexLoops.fromHex_sum`
(specification `Fv256.C.parseHex`).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.C Fv256.Arm64.SetFromHexLoops

namespace Fv256.Arm64.SetFromHex

theorem dataLoaded_write {p : Program} {m : Memory} (h : p.DataLoaded m) {a n : Nat} (v : Nat)
    (hw : m.accessible a n true = true) : p.DataLoaded (m.writeLE a n v) := by
  intro d hd
  obtain ⟨hreg, hbytes⟩ := h d hd
  have hreg' := hreg
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg'
  obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, _⟩, hro⟩⟩ := hreg'
  have hw' := hw
  simp only [Memory.accessible, Bool.and_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hw'
  refine ⟨hreg, fun i hi => ?_⟩
  have hx : a + n ≤ d.base + i ∨ d.base + i < a := by
    rcases hw'.2 r hr with (h1 | h1) | h1
    · rw [hro] at h1; cases h1
    · omega
    · omega
  rw [Memory.bytes_writeLE_outside _ (by omega)]
  exact hbytes i hi

/-- `fromHex_sum` with the postcondition written out (a callee summary's postcondition must be an explicit
conjunction for the symbolic executor to unpack it). -/
theorem fromHex_summary (z hp len : BitVec 64) :
    Summary Extracted.program fh (FromHexPre z hp len)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) :=
  by
    have h := fromHex_sum [] z hp len
    rw [link_nil] at h
    exact h

set_option maxHeartbeats 16000000 in
theorem correctness (z hp len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, hp, len]
      (fun s => GuardOK s 48 ∧ StackOK s 72 24 ∧ Ptr32 s.mem z true ∧ Ptr s.mem hp len.toNat false ∧
        Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
        (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        Disjoint z.toNat 32 hp.toNat len.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 72) 96 ∧
        Disjoint hp.toNat len.toNat (s.sp.toNat - 72) 96 ∧ Disjoint z.toNat 32 errBase 96 ∧
        Disjoint errBase 96 (s.sp.toNat - 72) 96 ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 72) 96)
      (fun s s' =>
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
        MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 72, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hps, hps'⟩, hd, herr, hnn, hd1, hd2, hd3, hd4, hd5, hd6⟩
  simp only [errBase_val, tabBase_val] at *
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3 hd4 hd5 hd6
  have hnn' : ∀ e, e < 6 → ¬ (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 hp.toNat).readLE (errAddrOf e) 8 = 0 := by
    intro e he
    have hb := errAddrOf_bounds e
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact hnn e he
  have htb : ∀ c, c < 256 → s.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255 := tab_vals hd
  have hSt0 : s.mem.accessible 1002789 256 false = true := accessible_of_dataRead hd tab_isSome
  have hzt : z.toNat + 32 ≤ 1002789 ∨ 1002789 + 256 ≤ z.toNat := disj_data hd (t := 1002789) (k := 256) tab_isSome hz
  have hst : s.sp.toNat - 72 + 96 ≤ 1002789 ∨ 1002789 + 256 ≤ s.sp.toNat - 72 :=
    disj_data hd (t := 1002789) (k := 256) tab_isSome hw
  have htb' : ∀ c, c < 256 → (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 hp.toNat).readLE (1002789 + c) 1 =
        (hexNib c).getD 255 := by
    intro c hc
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact htb c hc
  janus_run calls [fromHex_summary z hp len]
  rename_i hpcA hpcB hsp hr28 hr29 hr30 hr18 hE hfr hOK
  have hB : parseHex (bytesAt (((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 hp.toNat) hp.toNat) len.toNat =
      parseHex (bytesAt s.mem hp.toNat) len.toNat := by
    apply parseHex_congr
    intro k hk
    unfold bytesAt
    rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  have hEE : ∀ e, ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 hp.toNat).readLE (errAddrOf e) 8 =
        s.mem.readLE (errAddrOf e) 8) ∧
      ((((s.mem.writeLE (BitVec.toNat s.sp - 48) 8 ret).writeLE (BitVec.toNat s.sp - 56) 8
        (BitVec.toNat (s.regs 29))).writeLE (BitVec.toNat s.sp + 16) 8 hp.toNat).readLE (errAddrOf e + 8) 8 =
        s.mem.readLE (errAddrOf e + 8) 8) := by
    intro e
    have hb := errAddrOf_bounds e
    constructor
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega),
        Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  rw [hB] at hE hOK
  have hmf : MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24),
      (s.sp.toNat - 72, s.sp.toNat)] := by
    refine MemFrame.trans (rs := [(s.sp.toNat - 56, s.sp.toNat - 40), (s.sp.toNat + 16, s.sp.toNat + 24)]) ?_ hfr ?_
    · exact (((MemFrame.refl s.mem _).writeLE _ (r := (s.sp.toNat - 56, s.sp.toNat - 40)) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat - 56, s.sp.toNat - 40)) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := (s.sp.toNat + 16, s.sp.toNat + 24)) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)
    · intro a n h
      simp only [outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, h3, -⟩ := h
      refine ⟨⟨?_, ?_, trivial⟩, ?_, ?_, ?_, trivial⟩ <;> omega
  refine And.intro ?_ (And.intro ?_ hmf)
  · intro v hv
    obtain ⟨a, b, c⟩ := hOK v hv
    exact ⟨by rw [a], by rw [b], c⟩
  · intro e he
    obtain ⟨a, b⟩ := hE e he
    rw [(hEE e).1] at a
    rw [(hEE e).2] at b
    exact ⟨a, b⟩


namespace Witness

/-- the string `"0x1f"` at `haddr`, and non-nil package error variables at `1792784 + 16 k` -/
def wEntries : List (Nat × Nat) :=
  [(0x3100000, 0x30), (0x3100001, 0x78), (0x3100002, 0x31), (0x3100003, 0x66),
   (1792784, 1), (1792800, 1), (1792816, 1), (1792832, 1), (1792848, 1), (1792864, 1)]

def ret : Nat := 0x1000
def sp0 : Nat := 0x1000000
def g0 : Nat := 0x2000000
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((wEntries.lookup a).getD 0)

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def zp : BitVec 64 := BitVec.ofNat 64 0x3000000
def hpp : BitVec 64 := BitVec.ofNat 64 0x3100000

def s0 : State :=
  { regs := fun i => if i = 0 then zp else if i = 1 then hpp else if i = 2 then 4 else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 72, 96, true⟩, ⟨g0, 0x100, false⟩, ⟨0x3000000, 32, true⟩, ⟨0x3100000, 4, false⟩,
      ⟨1792784, 96, false⟩] ++ dregs⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [zp, hpp, 4] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 48 ∧ StackOK s0 72 24 ∧ Ptr32 s0.mem zp true ∧ Ptr s0.mem hpp (4 : BitVec 64).toNat false ∧
    Extracted.program.DataLoaded s0.mem ∧ s0.mem.accessible errBase 96 false = true ∧
    (∀ e, e < 6 → s0.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
    Disjoint zp.toNat 32 hpp.toNat (4 : BitVec 64).toNat ∧ Disjoint zp.toNat 32 (s0.sp.toNat - 72) 96 ∧
    Disjoint hpp.toNat (4 : BitVec 64).toNat (s0.sp.toNat - 72) 96 ∧ Disjoint zp.toNat 32 errBase 96 ∧
    Disjoint errBase 96 (s0.sp.toNat - 72) 96 ∧
    Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - 72) 96 := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩, dataLoaded, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
    all_goals decide
  all_goals (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z hp len : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, hp, len] s ∧
    (GuardOK s 48 ∧ StackOK s 72 24 ∧ Ptr32 s.mem z true ∧ Ptr s.mem hp len.toNat false ∧
      Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
      (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
      Disjoint z.toNat 32 hp.toNat len.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 72) 96 ∧
      Disjoint hp.toNat len.toNat (s.sp.toNat - 72) 96 ∧ Disjoint z.toNat 32 errBase 96 ∧
      Disjoint errBase 96 (s.sp.toNat - 72) 96 ∧
      Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 72) 96) :=
  ⟨ret, s0, zp, hpp, 4, hret, setup, pre⟩

set_option maxRecDepth 100000 in
/-- `"0x1f"` parses to `31`: the call returns no error and stores `31`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem zp.toNat = 31 := by
  refine (correctness zp hpp 4 ret hret s0 setup pre).mono ?_
  intro s' h
  have hb : ∀ k, bytesAt s0.mem hpp.toNat k = s0.mem.readLE (hpp.toNat + k) 1 := fun k => rfl
  have hp : parseHex (bytesAt s0.mem hpp.toNat) (4 : BitVec 64).toNat = Except.ok 31 := by
    show parseHex (bytesAt s0.mem hpp.toNat) 4 = _
    rw [pe_body _ _ (by decide) (by decide) (by rw [hb]; decide) (Or.inl (by rw [hb]; decide))
      (fun _ => by rw [hb]; decide)]
    have hall : allHex (bytesAt s0.mem hpp.toNat) 2 4 := by
      intro k h1 h2
      have : k = 2 ∨ k = 3 := by omega
      rcases this with rfl | rfl <;> (rw [hb]; decide)
    rw [if_pos hall]
    congr 1
  obtain ⟨a, b, c⟩ := h.2.1 31 hp
  exact ⟨h.1, a, b, c⟩

end Witness

end Fv256.Arm64.SetFromHex
