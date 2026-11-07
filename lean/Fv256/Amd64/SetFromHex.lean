import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.SumC64
import Fv256.Amd64.SetFromHexLoops

/-!
# `(*uint256.Int).SetFromHex(hex string) error` (amd64)

The wrapper around the non-inlined `fromHex`; the parse itself is the callee summary `SetFromHexLoops.fromHex_sum`
(specification `Fv256.C.parseHex`).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.C Fv256.Amd64.SetFromHexLoops

namespace Fv256.Amd64.SetFromHex

set_option maxRecDepth 100000 in
theorem tabData : ∀ c, c < 256 → (dataRead Extracted.program (5176782 + c) 1).isSome = true ∧
    dataReadD Extracted.program (5176782 + c) 1 = (hexNib c).getD 255 := by
  decide

theorem tab_vals {m : Janus.Arm64.Memory} (h : Extracted.program.DataLoaded m) :
    ∀ c, c < 256 → m.readLE (5176782 + c) 1 = (hexNib c).getD 255 := by
  intro c hc
  obtain ⟨h1, h2⟩ := tabData c hc
  rw [readLE_dataReadD h _ _ h1, h2]

/-- `fromHex_sum` with the postcondition written out (a callee summary's postcondition must be an explicit
conjunction for the symbolic executor to unpack it). -/
theorem fromHex_summary (z hp len : BitVec 64) :
    Summary Extracted.program fh (FromHexPre z hp len)
      (fun s s' => s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
        s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
        Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
          ((s.regs 4).toNat - 8, (s.regs 4).toNat)] ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) :=
  by
    have h := fromHex_sum [] z hp len
    rw [link_nil] at h
    exact h

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem correctness (z hp len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, hp, len]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 48 24 ∧ Buffer s z 32 true ∧ Buffer s hp len.toNat false ∧
        Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
        (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
        (z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
        (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
        (z.toNat + 32 ≤ errBase ∨ (errBase + 96) ≤ z.toNat) ∧
        ((errBase + 96) ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ errBase))
      (fun s s' =>
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8)) ∧
        Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
          ((s.regs 4).toNat - 48, (s.regs 4).toNat)]) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hpw, hps⟩, hd, herr, hnn, hd1, hd2, hd3, hd4, hd5⟩
  simp only [errBase_val, tabBase_val] at *
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd2 hd3 hd5
  have htb : ∀ c, c < 256 → s.mem.readLE (5176782 + c) 1 = (hexNib c).getD 255 := tab_vals hd
  -- the hex table object is found by its symbol (`tabBase`), not by its position in `Extracted.data`
  obtain ⟨dt, hdt, hdb, hdl⟩ : ∃ d ∈ Extracted.program.data, d.base = tabBase ∧ d.bytes.length = 256 := by decide
  have hdisj : ∀ {a n : Nat}, s.mem.accessible a n true = true → a + n ≤ 5176782 ∨ 5176782 + 256 ≤ a := by
    intro a n hw
    obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdt
    have := disjoint_of_dataLoaded hd k hk hw
    rw [hkd, hdb, hdl, tabBase_val] at this
    exact this
  have hSt0 : s.mem.accessible 5176782 256 false = true := by
    have := GoABI.DataLoaded.accessible hd hdt
    rw [hdb, hdl, tabBase_val] at this
    exact this
  have hzt : z.toNat + 32 ≤ 5176782 ∨ 5176782 + 256 ≤ z.toNat := hdisj hz
  have hst : (s.regs 4).toNat - 48 + 72 ≤ 5176782 ∨ 5176782 + 256 ≤ (s.regs 4).toNat - 48 := hdisj hacc
  have htb' : ∀ c, c < 256 → (((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 16) 8 hp.toNat).writeLE ((s.regs 4).toNat - 40) 8 4922296).readLE (5176782 + c) 1 =
      (hexNib c).getD 255 := by
    intro c hc
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact htb c hc
  have hnn' : ∀ e, e < 6 → ¬ (((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
      ((s.regs 4).toNat + 16) 8 hp.toNat).writeLE ((s.regs 4).toNat - 40) 8 4922296).readLE (errAddrOf e) 8 = 0 := by
    intro e he
    have hb := errAddrOf_bounds e
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    exact hnn e he
  janus64_run calls [fromHex_summary z hp len]
  all_goals
    rename_i hrip hr4 hr5 hr14 hx hdf' hfs hE hfr2 hOK
    have hB : parseHex (bytesAt (((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
        ((s.regs 4).toNat + 16) 8 hp.toNat).writeLE ((s.regs 4).toNat - 40) 8 4922296) hp.toNat) len.toNat =
        parseHex (bytesAt s.mem hp.toNat) len.toNat := by
      apply parseHex_congr
      intro k hk
      unfold bytesAt
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    have hEE : ∀ e, e < 6 → ((((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
        ((s.regs 4).toNat + 16) 8 hp.toNat).writeLE ((s.regs 4).toNat - 40) 8 4922296).readLE (errAddrOf e) 8 =
        s.mem.readLE (errAddrOf e) 8) ∧
        ((((Janus.Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE
        ((s.regs 4).toNat + 16) 8 hp.toNat).writeLE ((s.regs 4).toNat - 40) 8 4922296).readLE (errAddrOf e + 8) 8 =
        s.mem.readLE (errAddrOf e + 8) 8) := by
      intro e he
      have hb := errAddrOf_bounds e
      constructor <;> simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [hB] at hE hOK
    have hmf : Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
        ((s.regs 4).toNat - 48, (s.regs 4).toNat)] := by
      refine Janus.MemFrame.trans (rs := [((s.regs 4).toNat - 48, (s.regs 4).toNat), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24)]) ?_ hfr2 ?_
      · exact (((Janus.MemFrame.refl s.mem _).writeLE _ (r := ((s.regs 4).toNat - 48, (s.regs 4).toNat)) (by simp)
          (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24))
          (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat - 48, (s.regs 4).toNat))
          (by simp) (by dsimp only; omega) (by dsimp only; omega)
      · intro a n h
        simp only [Janus.outside_cons, Janus.outside_nil] at h ⊢
        obtain ⟨h1, h2, h3, -⟩ := h
        refine ⟨⟨?_, ?_, trivial⟩, ?_, ?_, ?_, trivial⟩ <;> omega
    refine And.intro ?_ (And.intro ?_ hmf)
    · intro v hv
      obtain ⟨a, b, c⟩ := hOK v hv
      exact ⟨by rw [a], by rw [b], c⟩
    · intro e he
      have hlt := parseHex_error_lt _ _ _ he
      obtain ⟨a, b⟩ := hE e he
      rw [(hEE e hlt).1] at a
      rw [(hEE e hlt).2] at b
      exact ⟨a, b⟩


namespace Witness

/-- the string `"0x1f"` at `0x30800`, and non-nil package error variables at `5995344 + 16 k` -/
def wEntries : List (Nat × Nat) :=
  [(0x30800, 0x30), (0x30801, 0x78), (0x30802, 0x31), (0x30803, 0x66),
   (5995344, 1), (5995360, 1), (5995376, 1), (5995392, 1), (5995408, 1), (5995424, 1)]

def ret : Nat := 0x200000
def sp0 : Nat := 0x1000000
def g0 : Nat := 0x2000000
def dsegs : List Janus.DataSegment := Extracted.data

def bytes (a : Nat) : Janus.Arm64.Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => BitVec.ofNat 8 ((wEntries.lookup a).getD 0)

def dregs : List Janus.Arm64.Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def zp : BitVec 64 := BitVec.ofNat 64 0x3000000
def hpp : BitVec 64 := BitVec.ofNat 64 0x30800

def s0 : State :=
  { regs := fun i => if i = 0 then zp else if i = 3 then hpp else if i = 1 then 4 else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 48, 72, true⟩, ⟨g0, 0x100, false⟩, ⟨0x3000000, 32, true⟩, ⟨0x30800, 4, false⟩,
      ⟨5995344, 96, false⟩] ++ dregs⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

set_option maxRecDepth 100000 in
theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [zp, hpp, 4] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Janus.Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 48 24 ∧ Buffer s0 zp 32 true ∧ Buffer s0 hpp (4 : BitVec 64).toNat false ∧
    Extracted.program.DataLoaded s0.mem ∧ s0.mem.accessible 5995344 96 false = true ∧
    (∀ e, e < 6 → s0.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
    (zp.toNat + 32 ≤ hpp.toNat ∨ hpp.toNat + (4 : BitVec 64).toNat ≤ zp.toNat) ∧
    (zp.toNat + 32 ≤ (s0.regs 4).toNat - 48 ∨ (s0.regs 4).toNat + 24 ≤ zp.toNat) ∧
    (hpp.toNat + (4 : BitVec 64).toNat ≤ (s0.regs 4).toNat - 48 ∨ (s0.regs 4).toNat + 24 ≤ hpp.toNat) ∧
    (zp.toNat + 32 ≤ 5995344 ∨ 5995440 ≤ zp.toNat) ∧
    (5995440 ≤ (s0.regs 4).toNat - 48 ∨ (s0.regs 4).toNat + 24 ≤ 5995344) := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, dataLoaded, by decide, ?_,
    by decide, by decide, by decide, by decide, by decide⟩
  intro e he
  obtain rfl | rfl | rfl | rfl | rfl | rfl : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 := by omega
  all_goals decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z hp len : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, hp, len] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 48 24 ∧ Buffer s z 32 true ∧ Buffer s hp len.toNat false ∧
      Extracted.program.DataLoaded s.mem ∧ s.mem.accessible errBase 96 false = true ∧
      (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0) ∧
      (z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat) ∧
      (z.toNat + 32 ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
      (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
      (z.toNat + 32 ≤ errBase ∨ (errBase + 96) ≤ z.toNat) ∧
      ((errBase + 96) ≤ (s.regs 4).toNat - 48 ∨ (s.regs 4).toNat + 24 ≤ errBase)) :=
  ⟨ret, s0, zp, hpp, 4, hret, setup, hpre⟩

set_option maxRecDepth 100000 in
/-- `"0x1f"` parses to `31`: the call returns no error and stores `31`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem zp.toNat = 31 := by
  refine (correctness zp hpp 4 ret hret s0 setup hpre).mono ?_
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

end Fv256.Amd64.SetFromHex
