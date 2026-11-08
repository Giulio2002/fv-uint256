import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Spec
import Fv256.SpecE
import Fv256.UtilE
import Fv256.StrE
import Fv256.SpecTxt
import Fv256.Amd64.DecExt
import Fv256.GrabTac
import Fv256.ToyRuntime64
import Fv256.ToyRuntime64B
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
  have hFR : MemFrame ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 40) 8 4928627) s'.mem
      (rt ++ [((s.regs 4).toNat - 40 - 4568, (s.regs 4).toNat - 40 + 8)]) := by assumption
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

namespace Witness

open Fv256.ToyRuntime64

def hA : Nat := 0x600000
def hB : Nat := 0x610000
def rtT : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 8)]

/-- readiness of the toy runtime: a two-byte string, and both heap blocks writable -/
def Hw : RtReady := fun a _ sp view =>
  (∃ p, a = [0, p, 2]) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 8 ≤ hB ∨ hB + 8 ≤ sp)

def implAt : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := sbts2Code hA }, { name := "model-stb", base := stAddr, bytes := stb2Code hB }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem rtView_acc (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem model1 : RtContract64 (Extracted.program.link implAt) ssAddr rtT 4096 Hw
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  have hargs : argWords64 s 3 = [0, p, 2] := hp
  simp [slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8 hdA hdB
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 2 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
    refine MemFrame.trans (rs := rtIf true rtT ++ (calleeStack64 s 4096 3 ++ []))
      (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
      (MemFrame.of_writeLE _ _ (rs := rtIf true rtT ++ (calleeStack64 s 4096 3 ++ [])) (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)) ?_
    intro a n h; exact ⟨h, h⟩
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · rw [← h3]
      simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
    · right; right; right
      exact ⟨Nat.le_refl _, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩

theorem or_shift8 : ∀ a, a < 256 → ∀ b, b < 256 → (a % 4294967296 ||| (b % 4294967296) <<< 8 % 4294967296) = a + 256 * b := by
  decide +kernel

theorem byte_lt (b : BitVec 8) : b.toNat < 256 := by have := b.isLt; simpa using this

theorem model2 : RtContract64 (Extracted.program.link implAt) stAddr rtT 4096 Hw stringtoslicebyteSpec := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  have hargs : argWords64 s 3 = [0, p, 2] := hp
  simp [stringtoslicebyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 2 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
    rw [or_shift8 _ (byte_lt _) _ (byte_lt _)]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [← h3, or_shift8 _ (byte_lt _) _ (byte_lt _)]
    have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 3)) 2).length = 2 := by simp [Spec.strBytes]
    have hr : roundupsize 2 true = 8 := by decide
    refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by rw [hl, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
      refine ⟨byte_lt _, ?_⟩
      have := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3) + 1))
      omega
    · intro i hi
      simp [Arm64.Memory.writeLE]
      rw [if_pos (by omega)]
      have h0b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3)))
      have h1b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3) + 1))
      have e : 6356994 + i - 6356992 = i + 2 := by omega
      rw [e]
      have hp2 : 256 ^ 2 ≤ 256 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.div_eq_of_lt (by omega)]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zp then 10 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4608, 4608 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem hz : s0.mem.readLE arg.toNat 32 = 10 := by
  unfold s0 arg zp
  decide

theorem hdb : decBytes 10 = [49, 48] := by
  rw [decBytes_ge 10 (by omega)]
  simp [decBytes_lt 1 (by omega)]

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 (0x378 + 40) ∧ StackWritable s0 4608 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4608) (4608 + 8) rtT ∧ Outside 5163273 256 rtT ∧ Outside 5176582 256 rtT ∧
    (∀ r ∈ rtT, 32 ≤ r.1) ∧
    (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4608 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4608 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s0.mem.readLE arg.toNat 32 →
      Hw [0, (s0.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 40 - 0x178 - 8) (rtView rtT s0.mem)) ∧
    (100 ≤ s0.mem.readLE arg.toNat 32 → s0.mem.readLE arg.toNat 32 < 2 ^ 64 →
      Hw [0, (s0.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 40 - 384 - 0x58) (rtView rtT s0.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s0.mem M (rtT ++ [((s0.regs 4).toNat - 4608, (s0.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s0.mem.readLE arg.toNat 32)) →
      DecAt rtT 5163273 5176582 5134938 p l →
      Hw [0, p, l] (s0.regs 14).toNat ((s0.regs 4).toNat - 40) (rtView rtT M)) := by
  rw [hz]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => absurd h (by decide), fun h _ => absurd h (by decide), ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · intro M p l hMF hSO hDA
    rw [hdb] at hSO
    have hl : l = 2 := by have := hSO.1; simpa using this
    subst hl
    refine ⟨⟨p, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide
    · simp only [s0, sp0, hA]; decide
    · simp only [s0, sp0, hB]; decide

-- CALLSITE-BLOCK MarshalText.nonvacuous
def csSb : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 zp else if i = 1 then BitVec.ofNat 64 2 else if i = 4 then BitVec.ofNat 64 (sp0 - 432) else s0.regs i }

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre64 rtT 4096 Hw (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  have hargs : argWords64 csSb 3 = [0, zp, 2] := by
    unfold argWords64 csSb; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show Hw (argWords64 csSb 3) (csSb.regs 14).toNat (csSb.regs 4).toNat (rtView rtT csSb.mem)
      rw [hargs]
      refine ⟨⟨zp, rfl⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide, by decide, by decide⟩
    · trivial

def csSt : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 stAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 zp else if i = 1 then BitVec.ofNat 64 2 else if i = 4 then BitVec.ofNat 64 (sp0 - 48) else s0.regs i }

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSt_pre : RtPre64 rtT 4096 Hw (stringtoslicebyteSpec) csSt := by
  have hargs : argWords64 csSt 3 = [0, zp, 2] := by
    unfold argWords64 csSt; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [stringtoslicebyteSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show Hw (argWords64 csSt 3) (csSt.regs 14).toNat (csSt.regs 4).toNat (rtView rtT csSt.mem)
      rw [hargs]
      refine ⟨⟨zp, rfl⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide, by decide, by decide⟩
    · trivial

/-- The preconditions, the `slicebytetostring` and `stringtoslicebyte` contracts (toy runtime blocks, readiness `Hw`), and the readiness hypothesis
for the second call are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 40) ∧ StackWritable s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4608) (4608 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
    (∀ r ∈ rt, 32 ≤ r.1) ∧
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
      H [0, p, l] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt M))) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 ssAddr ∧ RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 stAddr ∧ RtPre64 rt 4096 H stringtoslicebyteSpec s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt, rtT, Hw, ret, s0, arg, model1, model2, ?w2, ?w3, pre,
    ⟨csSb, rfl, csSb_pre⟩,
    ⟨csSt, rfl, csSt_pre⟩,
    correctness implAt rtT Hw arg model1 model2 ret ?w2 s0 ?w3 pre⟩
  case w2 => exact by rw [linked_eq]; exact hret
  case w3 => exact by rw [linked_eq]; exact setup



/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/
open Fv256.ToyRuntime64 in
def Hw8 : RtReady := fun a _ sp view =>
  (∃ p, a = [0, p, 8]) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 8 ≤ hB ∨ hB + 8 ≤ sp)

open Fv256.ToyRuntime64 in
def implAt8 : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := sbts8Code hA }, { name := "model-stb", base := stAddr, bytes := stb8Code hB }]
def linked8 : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = Spec.strBytes m p 8 := by
  apply Janus.Spec.strBytes_congr
  intro i hi
  have := Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi
  exact this

theorem model1_8 : RtContract64 (Extracted.program.link implAt8) ssAddr rtT 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  have hargs : argWords64 s 3 = [0, p, 8] := hp
  simp [slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8 hdA hdB
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 8 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h3, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩

theorem model2_8 : RtContract64 (Extracted.program.link implAt8) stAddr rtT 4096 Hw8 stringtoslicebyteSpec := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc] at ha
  obtain ⟨⟨p, hp⟩, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  have hargs : argWords64 s 3 = [0, p, 8] := hp
  simp [stringtoslicebyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hp hstr hbuf hdis
  obtain ⟨h0, h3, h1⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 3).toNat 8 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h3]
    have hr : roundupsize 8 true = 8 := by decide
    refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by simp [Spec.strBytes, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · rw [copy8_bytes]
    · intro i hi
      omega

def bytes8 (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zp then 0x80 else if a = zp + 1 then 0x96 else if a = zp + 2 then 0x98 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def s08 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes8, [⟨sp0 - 4608, 4608 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

theorem hret8 : RetAddr linked8 ret := RetAddr.of_check (by decide)

theorem setup8 : CallSetup (linked8.withExit ret) Extracted.entry [arg] s08 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded8 : Extracted.program.DataLoaded s08.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

theorem hz8 : s08.mem.readLE arg.toNat 32 = 10000000 := by
  unfold s08 arg zp
  decide

theorem hdl8 : decLen 10000000 = 8 := by
  simp (disch := omega) [decLen_ge, decLen_lt]

set_option maxRecDepth 100000 in
theorem pre8 : StackGuardOK s08 (0x378 + 40) ∧ StackWritable s08 4608 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside ((s08.regs 4).toNat - 4608) (4608 + 8) rtT ∧ Outside 5163273 256 rtT ∧ Outside 5176582 256 rtT ∧
    (∀ r ∈ rtT, 32 ≤ r.1) ∧
    (s08.regs 4).toNat % 8 = 0 ∧ Buffer s08 arg 32 false ∧
    (arg.toNat + 32 ≤ (s08.regs 4).toNat - 4608 ∨ (s08.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 14).toNat + 24 ≤ (s08.regs 4).toNat - 4608 ∨ (s08.regs 4).toNat + 8 ≤ (s08.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s08.mem.readLE arg.toNat 32 →
      Hw8 [0, (s08.regs 4).toNat - 40 - 0x178 + 86 + (98 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 40 - 0x178 - 8) (rtView rtT s08.mem)) ∧
    (100 ≤ s08.mem.readLE arg.toNat 32 → s08.mem.readLE arg.toNat 32 < 2 ^ 64 →
      Hw8 [0, (s08.regs 4).toNat - 40 - 384 - 0x20 + (24 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 40 - 384 - 0x58) (rtView rtT s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT ++ [((s08.regs 4).toNat - 4608, (s08.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s08.mem.readLE arg.toNat 32)) →
      DecAt rtT 5163273 5176582 5134938 p l →
      Hw8 [0, p, l] (s08.regs 14).toNat ((s08.regs 4).toNat - 40) (rtView rtT M)) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => absurd h (by decide), fun _ _ => ⟨⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · rw [rtView_acc]; decide
  · rw [rtView_acc]; decide
  · simp only [s08, sp0, hA]; decide
  · simp only [s08, sp0, hB]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨⟨p, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide
    · simp only [s08, sp0, hA]; decide
    · simp only [s08, sp0, hB]; decide

-- CALLSITE-BLOCK MarshalText.big
def csSb8 : Amd64.State :=
  { s08 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 zp else if i = 1 then BitVec.ofNat 64 8 else if i = 4 then BitVec.ofNat 64 (sp0 - 432) else s08.regs i }

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSb8_pre : RtPre64 rtT 4096 Hw8 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb8 := by
  have hargs : argWords64 csSb8 3 = [0, zp, 8] := by
    unfold argWords64 csSb8; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show Hw8 (argWords64 csSb8 3) (csSb8.regs 14).toNat (csSb8.regs 4).toNat (rtView rtT csSb8.mem)
      rw [hargs]
      refine ⟨⟨zp, rfl⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide, by decide, by decide⟩
    · trivial

def csSt8 : Amd64.State :=
  { s08 with rip := BitVec.ofNat 64 stAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 zp else if i = 1 then BitVec.ofNat 64 8 else if i = 4 then BitVec.ofNat 64 (sp0 - 48) else s08.regs i }

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSt8_pre : RtPre64 rtT 4096 Hw8 (stringtoslicebyteSpec) csSt8 := by
  have hargs : argWords64 csSt8 3 = [0, zp, 8] := by
    unfold argWords64 csSt8; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [stringtoslicebyteSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show Hw8 (argWords64 csSt8 3) (csSt8.regs 14).toNat (csSt8.regs 4).toNat (rtView rtT csSt8.mem)
      rw [hargs]
      refine ⟨⟨zp, rfl⟩, by rw [rtView_acc]; decide, by rw [rtView_acc]; decide, by decide, by decide⟩
    · trivial

/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) stAddr rt 4096 H stringtoslicebyteSpec ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 40) ∧ StackWritable s 4608 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4608) (4608 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
    (∀ r ∈ rt, 32 ≤ r.1) ∧
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
      H [0, p, l] (s.regs 14).toNat ((s.regs 4).toNat - 40) (rtView rt M))) ∧
    100 ≤ s.mem.readLE z.toNat 32 ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 ssAddr ∧ RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 stAddr ∧ RtPre64 rt 4096 H stringtoslicebyteSpec s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (decBytes (valueAt s z 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4608, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt8, rtT, Hw8, ret, s08, arg, model1_8, model2_8, ?w2, ?w3, pre8, ?w5,
    ⟨csSb8, rfl, csSb8_pre⟩,
    ⟨csSt8, rfl, csSt8_pre⟩,
    correctness implAt8 rtT Hw8 arg model1_8 model2_8 ret ?w2 s08 ?w3 pre8⟩
  case w2 => exact by rw [linked_eq8]; exact hret8
  case w3 => exact by rw [linked_eq8]; exact setup8
  case w5 => exact by rw [hz8]; decide
end Witness

end Fv256.Amd64.MarshalText
