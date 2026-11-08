import Extracted
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
# `(*uint256.Int).MarshalJSON() ([]byte, error)` (amd64): `"` digits `"`, error nil

**Guarantee.** Go doc: "MarshalJSON marshals using the 'decimal string' representation": `[]byte("\"" + z.Dec() + "\"")`, `nil`.
The code calls `Dec` and then `runtime.concatbyte3(nil, "\"", s, "\"")`.  Under the contracts of `slicebytetostring` and `concatbyte3` and
the readiness `H` for the second call (over every memory that is a frame of the entry memory and every string `(p, l)` that `Dec` can
return), the call returns `(ptr, len, cap)`: `len ≤ cap`, `[ptr, ptr+cap)` writable and holding `marshalJSONBytes z` in its first `len`
bytes and zero after (`BytesHold`), the error `(RDI, RSI) = (0, 0)` (nil), and no byte outside the runtime ranges and the frame changes.
The quote string is the program's read-only datum at `5181392` (`"`); its bytes are unchanged by the runtime (`Outside 5181392 32 rt`).
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts
open Fv256.E
open Fv256.Amd64.Dec

namespace Fv256.Amd64.MarshalJSON

abbrev cbAddr : Nat := Extracted.program.contractAddr "runtime.concatbyte3"

theorem roundupsize_pos_small : ∀ n, n < 82 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract64 (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s (0x378 + 72) ∧ StackWritable s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside ((s.regs 4).toNat - 4640) (4640 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧
        Outside 5181392 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
          H [0, (s.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 72 - 0x178 - 8) (rtView rt s.mem)) ∧
        (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
          H [0, (s.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
            (s.regs 14).toNat ((s.regs 4).toNat - 72 - 384 - 0x58) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) →
          StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
          DecAt rt 5163273 5176582 5134938 p l →
          H [0, 5181392, 1, p, l, 5181392, 1] (s.regs 14).toNat ((s.regs 4).toNat - 72) (rtView rt M)))
      (fun s s' => BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (marshalJSONBytes (s.mem.readLE z.toNat 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hout, hrt1, hrt2, hrt3, hrt32, hal, ⟨hzn, hza⟩, hzd, hgd, hH, hH1, hH2⟩
  janus64_intro hs
  have hdE : decE = 4931168 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_run [hdE] until [4928749] calls [dec_summary_ext impl rt H z hc]
  have hFR : MemFrame ((Arm64.Memory.writeLE s.mem ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 72) 8 4928723) s'.mem
      (rt ++ [((s.regs 4).toNat - 72 - 4568, (s.regs 4).toNat - 72 + 8)]) := by assumption
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
  -- layout-robust: find the 32-byte quote object by its symbol (not by its position in `Extracted.data`)
  obtain ⟨dq, hqmem, hqbase, hqlen, hqb0⟩ : ∃ d ∈ Extracted.program.data,
      d.base = Extracted.dataAddr.«.rodata#c3589c3e» ∧ d.bytes.length = 32 ∧ d.bytes[0]! = 34 := by decide
  have hsym : Extracted.dataAddr.«.rodata#c3589c3e» = 5181392 := by decide
  rw [hsym] at hqbase
  have hqj := dataLoaded_disjoint hd hqmem hwa
  rw [hqbase, hqlen] at hqj
  have hqacc : s.mem.accessible 5181392 1 false = true := by
    have := DataLoaded.accessible hd hqmem
    rw [hqbase, hqlen] at this
    exact accessible_sub this (Or.inl rfl) (by omega) (by omega)
  have hqbyte : s.mem.readLE 5181392 1 = 34 := by
    have b0 := DataLoaded.byte hd hqmem 0 (by rw [hqlen]; omega)
    rw [hqbase, Nat.add_zero] at b0
    rw [b0]
    simpa [getElem!_pos dq.bytes 0 (by rw [hqlen]; omega)] using hqb0
  have hOut : BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 3) ≤ BitVec.toNat (s.regs 4) - 4640 ∨
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
  have hMF : MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) := by
    have h1 : MemFrame s.mem ((s.mem.writeLE ((s.regs 4).toNat - 8) 8 (s.regs 5).toNat).writeLE ((s.regs 4).toNat - 72) 8 4928723)
        (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) := by
      refine MemFrame.trans (rs := rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)])
        (MemFrame.of_writeLE s.mem _ (r := ((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) (r := ((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) hFR (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, trivial⟩)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  simp (disch := omega) only [valueAt, Janus.Arm64.Memory.readLE_writeLE_of_disjoint] at hl1 hl2 hl3 hl4
  have hSO' : StrOut s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 3)) (decBytes (s.mem.readLE z.toNat 32)) :=
    ⟨hl1, hl2, fun h => by rw [hMF.accessible]; exact hl3 h, hl4⟩
  have hH2' := hH2 s'.mem _ _ hMF hSO' hDA
  have hqM : s'.mem.readLE 5181392 1 = 34 := by
    have hqo : Outside 5181392 1 (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) := by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨Outside.of_sub hrt3 (by omega) (by omega), by omega, trivial⟩
    rw [hMF.readLE _ _ hqo, hqbyte]
  have hqacc' : s'.mem.accessible 5181392 1 false = true := by rw [hMF.accessible]; exact hqacc
  janus64_run calls [hc2]
  grab_last_const Janus.Contracts.CatBytesOut as hCB
  grab_last_const Janus.MemFrame as hF2
  have hq1 : Spec.strBytes s'.mem 5181392 1 = [34] := by
    simp only [Spec.strBytes, List.range_one, List.map_cons, List.map_nil]
    rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hqM]
  rw [hq1, hl4] at hCB
  have hvlt : s.mem.readLE z.toNat 32 < 2 ^ 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
  have hd78 : decLen (s.mem.readLE z.toNat 32) ≤ 78 :=
    decLen_le_of_lt_pow _ 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
  have hd1 := decLen_pos (s.mem.readLE z.toNat 32)
  have hbs : ([34] ++ (decBytes (s.mem.readLE z.toNat 32) ++ [34])) = marshalJSONBytes (s.mem.readLE z.toNat 32) := rfl
  have hbl : (marshalJSONBytes (s.mem.readLE z.toNat 32)).length = decLen (s.mem.readLE z.toNat 32) + 2 := marshalJSONBytes_length _
  rw [hbs] at hCB
  obtain ⟨hlen, -, -, hr2, hBH⟩ := hCB
  obtain ⟨hr2a, -⟩ := hr2 (by omega) (Or.inl rfl)
  have hrp := roundupsize_pos_small (marshalJSONBytes (s.mem.readLE z.toNat 32)).length (by omega) (by omega)
  have hBH' := hBH (by omega)
  have h1 : MemFrame s'.mem (Arm64.Memory.writeLE s'.mem ((s.regs 4).toNat - 72) 8 4928754)
      (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) :=
    MemFrame.of_writeLE s'.mem _ (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)
  have h2 := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) hF2 (fun a n h => by
    simp only [outside_append, outside_cons] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, by omega, by omega, trivial⟩)
  exact ⟨hBH', hMF.trans (h1.trans h2 fun a n h => ⟨h, h⟩) fun a n h => ⟨h, h⟩⟩

namespace Witness

open Fv256.ToyRuntime64

def hA : Nat := 0x600000
def hB : Nat := 0x610000
def rtT : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 8)]

/-- readiness of the toy runtime: a two-byte string (slicebytetostring) or the quote, a two-byte string and the quote (concatbyte3), and both heap blocks writable -/
def Hw : RtReady := fun a _ sp view =>
  ((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, 5181392, 1, p, 2, 5181392, 1])) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 8 ≤ hB ∨ hB + 8 ≤ sp)

def implAt : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := sbts2Code hA }, { name := "model-cb", base := cbAddr, bytes := cat4Code hB }]
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
  obtain ⟨hshape, hA8, hB8, hdA, hdB⟩ := ha
  have hlen3 : (argWords64 s 3).length = 3 := by simp [argWords64, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords64 s 3 = [0, p, 2] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp⟩
    · have hp' : argWords64 s 3 = _ := hp
      rw [hp'] at hlen3; simp at hlen3
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

theorem byte_lt (b : BitVec 8) : b.toNat < 256 := by have := b.isLt; simpa using this

theorem div256 (r k : Nat) (hr : r < 256) : (r + 256 * k) / 256 = k ∧ (r + 256 * k) % 256 = r := by
  omega

theorem byte4_bytes (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    ((a + b * 256 + c * 65536 + a * 16777216) % 4294967296) % 256 = a ∧
    ((a + b * 256 + c * 65536 + a * 16777216) % 4294967296) / 256 % 256 = b ∧
    ((a + b * 256 + c * 65536 + a * 16777216) % 4294967296) / 65536 % 256 = c ∧
    ((a + b * 256 + c * 65536 + a * 16777216) % 4294967296) / 16777216 % 256 = a := by
  have hv : (a + b * 256 + c * 65536 + a * 16777216) % 4294967296 = a + 256 * (b + 256 * (c + 256 * a)) := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hv]
  obtain ⟨d1, m1⟩ := div256 a (b + 256 * (c + 256 * a)) ha
  obtain ⟨d2, m2⟩ := div256 b (c + 256 * a) hb
  obtain ⟨d3, m3⟩ := div256 c a hc
  have e2 : (a + 256 * (b + 256 * (c + 256 * a))) / 65536 = c + 256 * a := by
    rw [show (65536 : Nat) = 256 * 256 from rfl, ← Nat.div_div_eq_div_mul, d1, d2]
  have e3 : (a + 256 * (b + 256 * (c + 256 * a))) / 16777216 = a := by
    rw [show (16777216 : Nat) = 65536 * 256 from rfl, ← Nat.div_div_eq_div_mul, e2, d3]
  refine ⟨m1, ?_, ?_, ?_⟩
  · rw [d1, m2]
  · rw [e2, m3]
  · rw [e3]; exact Nat.mod_eq_of_lt ha


theorem model2 : RtContract64 (Extracted.program.link implAt) cbAddr rtT 4096 Hw (concatbyteSpec 3) := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw, rtView_acc] at ha
  obtain ⟨hshape, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  have hlen7 : (argWords64 s 7).length = 7 := by simp [argWords64, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords64 s 7 = [0, 5181392, 1, p, 2, 5181392, 1] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hp' : argWords64 s 7 = _ := hp
      rw [hp'] at hlen7; simp at hlen7
    · exact ⟨p, hp⟩
  have hargs : argWords64 s 7 = [0, 5181392, 1, p, 2, 5181392, 1] := hp
  have hargs' : argWords64 s (concatbyteSpec 3).nargs = [0, 5181392, 1, p, 2, 5181392, 1] := hp
  rw [hargs'] at hstr hbuf
  simp [strPairs, StrsIn, arg] at hstr hbuf
  simp [concatbyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp
  obtain ⟨h0, h3, h1, h7, h6, h8, h9⟩ := hp
  obtain ⟨⟨hq1, hq1a⟩, ⟨hp1, hp1a⟩, -⟩ := hstr
  have hqa : s.mem.accessible (s.regs 3).toNat 1 false = true := by rw [h3]; exact hq1a (by omega)
  have hqa8 : s.mem.accessible (s.regs 8).toNat 1 false = true := by rw [h8]; exact hq1a (by omega)
  have hpa : s.mem.accessible (s.regs 7).toNat 2 false = true := by rw [h7]; exact hp1a (by omega)
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h8, ← h3, ← h7]
    have hb0 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3)))
    have hb1 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 7)))
    have hb2 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 7) + 1))
    have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 3)) 1 ++ (Spec.strBytes s.mem (BitVec.toNat (s.regs 7)) 2 ++
        Spec.strBytes s.mem (BitVec.toNat (s.regs 3)) 1)).length = 4 := by simp [Spec.strBytes]
    have hr : roundupsize 4 true = 8 := by decide
    refine ⟨by rw [hl], ?_, ?_, ?_, ?_⟩
    · intro h; rw [hl] at h; omega
    · intro _ h; exact absurd rfl h
    · intro _ _; exact ⟨by rw [hl, hr], (6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩
    intro _
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
      generalize BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) = a at *
      generalize BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 7))) = b at *
      generalize BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 7) + 1)) = c at *
      have h4 := byte4_bytes a b c hb0 hb1 hb2
      refine ⟨by omega, h4.2.1, h4.2.2.1, h4.2.2.2⟩
    · intro i hi
      simp [Arm64.Memory.writeLE]
      rw [if_pos (by omega)]
      have e : 6356996 + i - 6356992 = i + 4 := by omega
      rw [e]
      have hp2 : 256 ^ 4 ≤ 256 ^ (i + 4) := Nat.pow_le_pow_right (by omega) (by omega)
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
    mem := ⟨bytes, [⟨sp0 - 4640, 4640 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

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
theorem pre : StackGuardOK s0 (0x378 + 72) ∧ StackWritable s0 4640 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 4640) (4640 + 8) rtT ∧ Outside 5163273 256 rtT ∧ Outside 5176582 256 rtT ∧ Outside 5181392 32 rtT ∧
    (∀ r ∈ rtT, 32 ≤ r.1) ∧
    (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
    (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4640 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4640 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s0.mem.readLE arg.toNat 32 →
      Hw [0, (s0.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 72 - 0x178 - 8) (rtView rtT s0.mem)) ∧
    (100 ≤ s0.mem.readLE arg.toNat 32 → s0.mem.readLE arg.toNat 32 < 2 ^ 64 →
      Hw [0, (s0.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s0.mem.readLE arg.toNat 32)), decLen (s0.mem.readLE arg.toNat 32)]
        (s0.regs 14).toNat ((s0.regs 4).toNat - 72 - 384 - 0x58) (rtView rtT s0.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s0.mem M (rtT ++ [((s0.regs 4).toNat - 4640, (s0.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s0.mem.readLE arg.toNat 32)) →
      DecAt rtT 5163273 5176582 5134938 p l →
      Hw [0, 5181392, 1, p, l, 5181392, 1] (s0.regs 14).toNat ((s0.regs 4).toNat - 72) (rtView rtT M)) := by
  rw [hz]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => absurd h (by decide), fun h _ => absurd h (by decide), ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · intro M p l hMF hSO hDA
    rw [hdb] at hSO
    have hl : l = 2 := by have := hSO.1; simpa using this
    subst hl
    refine ⟨Or.inr ⟨p, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide
    · simp only [s0, sp0, hA]; decide
    · simp only [s0, sp0, hB]; decide

/-- The preconditions, the `slicebytetostring` and `concatbyte3` contracts (toy runtime blocks, readiness `Hw`), and the readiness hypothesis
for the second call are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 72) ∧ StackWritable s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4640) (4640 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ Outside 5181392 32 rt ∧
    (∀ r ∈ rt, 32 ≤ r.1) ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      H [0, (s.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 72 - 0x178 - 8) (rtView rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (s.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 72 - 384 - 0x58) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l →
      H [0, 5181392, 1, p, l, 5181392, 1] (s.regs 14).toNat ((s.regs 4).toNat - 72) (rtView rt M))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (marshalJSONBytes (s.mem.readLE z.toNat 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt, rtT, Hw, ret, s0, arg, model1, model2, ?w2, ?w3, pre,
    correctness implAt rtT Hw arg model1 model2 ret ?w2 s0 ?w3 pre⟩
  case w2 => exact by rw [linked_eq]; exact hret
  case w3 => exact by rw [linked_eq]; exact setup



/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/

def rtT16 : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 16)]

theorem rtView_acc16 (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT16 m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

def Hw8 : RtReady := fun a _ sp view =>
  ((∃ p, a = [0, p, 8]) ∨ (∃ p, a = [0, 5181392, 1, p, 8, 5181392, 1])) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 16 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 16 ≤ hB ∨ hB + 16 ≤ sp)

open Fv256.ToyRuntime64 in
def implAt8 : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := sbts8Code hA }, { name := "model-cb", base := cbAddr, bytes := cat10Code hB }]
def linked8 : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = Spec.strBytes m p 8 := by
  apply Janus.Spec.strBytes_congr
  intro i hi
  exact Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi

theorem cat10_bytes (m : Janus.Arm64.Memory) (q1 q2 p B : Nat) :
    Spec.strBytes ((((m.writeLE (B + 8) 8 0).writeLE B 1 (m.bytes q1).toNat).writeLE (B + 1) 8 (m.readLE p 8)).writeLE (B + 9) 1 (m.bytes q2).toNat) B 10
      = Spec.strBytes m q1 1 ++ (Spec.strBytes m p 8 ++ Spec.strBytes m q2 1) := by
  have hb : ∀ j, j < 8 → BitVec.ofNat 8 (m.readLE p 8 / 256 ^ j) = m.bytes (p + j) :=
    fun j hj => Janus.Contracts.IfaceModel.byte_of_readLE m 8 p j hj
  simp only [Spec.strBytes, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    Janus.Arm64.Memory.writeLE]
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have h4 := hb 4 (by omega)
  have h5 := hb 5 (by omega)
  have h6 := hb 6 (by omega)
  have h7 := hb 7 (by omega)
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  have e4 := congrArg BitVec.toNat h4
  have e5 := congrArg BitVec.toNat h5
  have e6 := congrArg BitVec.toNat h6
  have e7 := congrArg BitVec.toNat h7
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.div_one, Nat.add_zero] at e0 e1 e2 e3 e4 e5 e6 e7
  simp
  rw [if_neg (by omega), if_neg (by omega)]
  omega


theorem model1_8 : RtContract64 (Extracted.program.link implAt8) ssAddr rtT16 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8, hdA, hdB⟩ := ha
  have hlen3 : (argWords64 s 3).length = 3 := by simp [argWords64, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords64 s 3 = [0, p, 8] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp⟩
    · have hp' : argWords64 s 3 = _ := hp
      rw [hp'] at hlen3; simp at hlen3
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
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT16, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h3, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT16, hA], by omega, by omega⟩

theorem model2_8 : RtContract64 (Extracted.program.link implAt8) cbAddr rtT16 4096 Hw8 (concatbyteSpec 3) := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  have hlen7 : (argWords64 s 7).length = 7 := by simp [argWords64, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords64 s 7 = [0, 5181392, 1, p, 8, 5181392, 1] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hp' : argWords64 s 7 = _ := hp
      rw [hp'] at hlen7; simp at hlen7
    · exact ⟨p, hp⟩
  have hargs : argWords64 s 7 = [0, 5181392, 1, p, 8, 5181392, 1] := hp
  have hargs' : argWords64 s (concatbyteSpec 3).nargs = [0, 5181392, 1, p, 8, 5181392, 1] := hp
  rw [hargs'] at hstr hbuf
  simp [strPairs, StrsIn, arg] at hstr hbuf
  simp [concatbyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp
  obtain ⟨h0, h3, h1, h7, h6, h8, h9⟩ := hp
  obtain ⟨⟨hq1, hq1a⟩, ⟨hp1, hp1a⟩, -⟩ := hstr
  have hqa : s.mem.accessible (s.regs 3).toNat 1 false = true := by rw [h3]; exact hq1a (by omega)
  have hqa8 : s.mem.accessible (s.regs 8).toNat 1 false = true := by rw [h8]; exact hq1a (by omega)
  have hpa : s.mem.accessible (s.regs 7).toNat 8 false = true := by rw [h7]; exact hp1a (by omega)
  janus64_run
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    repeat' first
      | exact MemFrame.refl _ _
      | (refine MemFrame.writeLE ?_ _ (r := (6356992, 6357008)) (by simp [rtIf, rtT16, hB]) (by omega) (by omega))
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h8, h3, h7]
    have hc := cat10_bytes s.mem 5181392 5181392 p 6356992
    simp only [Nat.reduceAdd] at hc
    have hl : (Spec.strBytes s.mem 5181392 1 ++ (Spec.strBytes s.mem p 8 ++ Spec.strBytes s.mem 5181392 1)).length = 10 := by simp [Spec.strBytes]
    have hr : roundupsize 10 true = 16 := by decide
    refine ⟨hl.symm, fun h => by omega, fun _ h => absurd rfl h, fun _ _ => ⟨by rw [hl, hr], (6356992, 6357008), by simp [rtT16, hB], by omega, by omega⟩, fun _ => ?_⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · exact hc
    · intro i hi
      have c1 : ¬ (6357001 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357001 + 1) := by omega
      have c2 : ¬ (6356993 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356993 + 8) := by omega
      have c3 : ¬ (6356992 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356992 + 1) := by omega
      have c4 : (6357000 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357000 + 8) := by omega
      simp only [Janus.Arm64.Memory.bytes_writeLE]
      rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
      simp

def bytes8 (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  if a = zp then 0x80 else if a = zp + 1 then 0x96 else if a = zp + 2 then 0x98 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def s08 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes8, [⟨sp0 - 4640, 4640 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 16, true⟩] ++ dregs⟩ }

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
theorem pre8 : StackGuardOK s08 (0x378 + 72) ∧ StackWritable s08 4640 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside ((s08.regs 4).toNat - 4640) (4640 + 8) rtT16 ∧ Outside 5163273 256 rtT16 ∧ Outside 5176582 256 rtT16 ∧ Outside 5181392 32 rtT16 ∧
    (∀ r ∈ rtT16, 32 ≤ r.1) ∧
    (s08.regs 4).toNat % 8 = 0 ∧ Buffer s08 arg 32 false ∧
    (arg.toNat + 32 ≤ (s08.regs 4).toNat - 4640 ∨ (s08.regs 4).toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 14).toNat + 24 ≤ (s08.regs 4).toNat - 4640 ∨ (s08.regs 4).toNat + 8 ≤ (s08.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s08.mem.readLE arg.toNat 32 →
      Hw8 [0, (s08.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 72 - 0x178 - 8) (rtView rtT16 s08.mem)) ∧
    (100 ≤ s08.mem.readLE arg.toNat 32 → s08.mem.readLE arg.toNat 32 < 2 ^ 64 →
      Hw8 [0, (s08.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s08.mem.readLE arg.toNat 32)), decLen (s08.mem.readLE arg.toNat 32)]
        (s08.regs 14).toNat ((s08.regs 4).toNat - 72 - 384 - 0x58) (rtView rtT16 s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT16 ++ [((s08.regs 4).toNat - 4640, (s08.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s08.mem.readLE arg.toNat 32)) →
      DecAt rtT16 5163273 5176582 5134938 p l →
      Hw8 [0, 5181392, 1, p, l, 5181392, 1] (s08.regs 14).toNat ((s08.regs 4).toNat - 72) (rtView rtT16 M)) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun h => absurd h (by decide), fun _ _ => ⟨Or.inl ⟨_, rfl⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB]; decide
  · rw [rtView_acc16]; decide
  · rw [rtView_acc16]; decide
  · simp only [s08, sp0, hA]; decide
  · simp only [s08, sp0, hB]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨Or.inr ⟨p, rfl⟩, ?_, ?_, ?_, ?_⟩
    · rw [rtView_acc16, hMF.accessible]; decide
    · rw [rtView_acc16, hMF.accessible]; decide
    · simp only [s08, sp0, hA]; decide
    · simp only [s08, sp0, hB]; decide

/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract64 (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s (0x378 + 72) ∧ StackWritable s 4640 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside ((s.regs 4).toNat - 4640) (4640 + 8) rt ∧ Outside 5163273 256 rt ∧ Outside 5176582 256 rt ∧ Outside 5181392 32 rt ∧
    (∀ r ∈ rt, 32 ≤ r.1) ∧
    (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
    (z.toNat + 32 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
    ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4640 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
    (2 ^ 64 ≤ s.mem.readLE z.toNat 32 →
      H [0, (s.regs 4).toNat - 72 - 0x178 + 86 + (98 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 72 - 0x178 - 8) (rtView rt s.mem)) ∧
    (100 ≤ s.mem.readLE z.toNat 32 → s.mem.readLE z.toNat 32 < 2 ^ 64 →
      H [0, (s.regs 4).toNat - 72 - 384 - 0x20 + (24 - decLen (s.mem.readLE z.toNat 32)), decLen (s.mem.readLE z.toNat 32)]
        (s.regs 14).toNat ((s.regs 4).toNat - 72 - 384 - 0x58) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) →
      StrOut M p l (decBytes (s.mem.readLE z.toNat 32)) →
      DecAt rt 5163273 5176582 5134938 p l →
      H [0, 5181392, 1, p, l, 5181392, 1] (s.regs 14).toNat ((s.regs 4).toNat - 72) (rtView rt M))) ∧
    100 ≤ s.mem.readLE z.toNat 32 ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ BytesHold s'.mem (s'.regs 0).toNat (s'.regs 3).toNat (s'.regs 1).toNat (marshalJSONBytes (s.mem.readLE z.toNat 32)) ∧
        s'.regs 7 = 0 ∧ s'.regs 6 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4640, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt8, rtT16, Hw8, ret, s08, arg, model1_8, model2_8, ?w2, ?w3, pre8, ?w5,
    correctness implAt8 rtT16 Hw8 arg model1_8 model2_8 ret ?w2 s08 ?w3 pre8⟩
  case w2 => exact by rw [linked_eq8]; exact hret8
  case w3 => exact by rw [linked_eq8]; exact setup8
  case w5 => exact by rw [hz8]; decide

end Witness

end Fv256.Amd64.MarshalJSON
