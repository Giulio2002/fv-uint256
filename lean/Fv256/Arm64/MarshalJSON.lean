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
import Fv256.ToyRuntimeArm64
import Fv256.ToyRuntimeArm64B

/-!
# `(*uint256.Int).MarshalJSON() ([]byte, error)` (arm64): `"` digits `"`, error nil

As the amd64 theorem (`Fv256.Amd64.MarshalJSON`): `[]byte("\"" + z.Dec() + "\"")`, `nil`, under the `slicebytetostring` and `concatbyte3`
contracts and the readiness `H` for the second call (a hypothesis over every memory that is a frame of the entry memory and every string
`(p, l)` that `Dec` can return).  The call returns `(ptr, len, cap)` (`X0, X1, X2`): `len ≤ cap`, `[ptr, ptr+cap)` writable and holding
`marshalJSONBytes z` in its first `len` bytes and zero after, the error `(X3, X4) = (0, 0)`, and no byte outside the runtime ranges and the
frame changes.  The quote string is the read-only datum at `1007400` (`"`), not runtime-owned (`Outside 1007400 32 rt`); the runtime ranges
lie above the first 32 bytes.
-/

open Janus Janus.Arm64 Janus.Tactic Janus.GoABI Janus.Spec Janus.Contracts
open Fv256.E
open Fv256.Arm64.Dec

namespace Fv256.Arm64.MarshalJSON

abbrev cbAddr : Nat := Extracted.program.contractAddr "runtime.concatbyte3"

theorem roundupsize_pos_small : ∀ n, n < 82 → 1 ≤ n → 0 < roundupsize n true := by decide +kernel

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 200000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (hc2 : RtContract (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s (688 + 80) ∧ StackOK s 4688 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4688) (4688 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧
        Outside 1007400 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (2 ^ 64 ≤ val256 s.mem z.toNat →
          H [0, s.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 80 - 384) (rtView rt s.mem)) ∧
        (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
          H [0, s.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
            (s.regs 28).toNat (s.sp.toNat - 80 - 384 - 96) (rtView rt s.mem)) ∧
        (∀ (M : Janus.Arm64.Memory) (p l : Nat),
          MemFrame s.mem M (rt ++ [(s.sp.toNat - 4688, s.sp.toNat + 8)]) →
          StrOut M p l (decBytes (val256 s.mem z.toNat)) →
          DecAt rt 989280 1002589 960826 p l →
          H [0, 1007400, 1, p, l, 1007400, 1] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt M)))
      (fun s s' => BytesHold s'.mem (s'.regs 0).toNat (s'.regs 1).toNat (s'.regs 2).toNat (marshalJSONBytes (val256 s.mem z.toNat)) ∧
        s'.regs 3 = 0 ∧ s'.regs 4 = 0 ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4688, s.sp.toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hst, hd, hout, hrt1, hrt2, hrt3, hrt32, ⟨hza, hzn⟩, hzd, hgd, hH, hH1, hH2⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, h4688, hsp2, hwa⟩ := hst
  simp only [val256, Fv256.Util.readLE_32] at hH hH1 ⊢
  have hdE : decE = 754624 := by unfold decE; decide
  have hcE : decE + 0x5000 < 2 ^ 47 := by decide
  janus_run [hdE] until [752508] calls [dec_summary_ext impl rt H z hc]
  have hFR : MemFrame ((s.mem.writeLE (BitVec.toNat s.sp - 80) 8 ret).writeLE (BitVec.toNat s.sp - 88) 8 (BitVec.toNat (s.regs 29))) s'.mem
      (rt ++ [(BitVec.toNat s.sp - 80 - 4608, BitVec.toNat s.sp - 80 - 8)]) := by assumption
  grab_last_const Fv256.E.DecAt as hDA
  grab_last_const Janus.Spec.strBytes as hSO
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hSO
  have hdL := Fv256.Arm64.LinkEq.DataLoaded.of_subset hLib.data hd
  have hj1 := dl_disjoint hdL digits_mem hwa
  have hj2 := dl_disjoint hdL smalls_mem hwa
  have hj3 := dl_disjoint hdL zeroDat_mem hwa
  rw [digits_base, digits_len] at hj1
  rw [smalls_base, smalls_len] at hj2
  rw [zeroDat_base, zeroDat_len] at hj3
  have hqmem : Extracted.data[5] ∈ Extracted.program.data := List.getElem_mem (by decide)
  have hqbase : Extracted.data[5].base = 1007400 := by decide
  have hqlen : Extracted.data[5].bytes.length = 32 := by decide
  have hqj := dl_disjoint hd hqmem hwa
  rw [hqbase, hqlen] at hqj
  have hqacc : s.mem.accessible 1007400 1 false = true := by
    have := dl_acc hd hqmem
    rw [hqbase, hqlen] at this
    exact accessible_sub this (Or.inl rfl) (by omega) (by omega)
  have hqbyte : s.mem.readLE 1007400 1 = 34 := by
    have b0 := dl_byte hd hqmem 0 (by rw [hqlen]; omega)
    rw [hqbase, Nat.add_zero] at b0
    rw [b0]
    have : Extracted.data[5].bytes[0]! = 34 := by decide
    simpa [getElem!_pos Extracted.data[5].bytes 0 (by rw [hqlen]; omega)] using this
  have hOut : BitVec.toNat (s'.regs 0) + BitVec.toNat (s'.regs 1) ≤ BitVec.toNat s.sp - 4688 ∨
      BitVec.toNat s.sp + 8 ≤ BitVec.toNat (s'.regs 0) := by
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := MemFrame.outside_mem hout hr
      omega
    all_goals omega
  have hrt32' : 32 ≤ BitVec.toNat (s'.regs 0) := by
    rcases hDA with ⟨r, hr, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hrt32 r hr
      omega
    all_goals omega
  have hMF : MemFrame s.mem s'.mem (rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) := by
    have h1 : MemFrame s.mem ((s.mem.writeLE (BitVec.toNat s.sp - 80) 8 ret).writeLE (BitVec.toNat s.sp - 88) 8 (BitVec.toNat (s.regs 29)))
        (rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) := by
      refine MemFrame.trans (rs := rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)])
        (MemFrame.of_writeLE s.mem _ (r := (BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) (r := (BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)) (List.mem_append_right _ (List.mem_singleton_self _)) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    have h2 := MemFrame.mono (rs' := rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) hFR (fun a n h => by
      simp only [outside_append, outside_cons] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, trivial⟩)
    exact h1.trans h2 fun a n h => ⟨h, h⟩
  have hSO' : StrOut s'.mem (BitVec.toNat (s'.regs 0)) (BitVec.toNat (s'.regs 1)) (decBytes (val256 s.mem z.toNat)) := by
    simp only [val256, Fv256.Util.readLE_32, Nat.reducePow] at hl1 hl4 ⊢
    exact ⟨hl1, hl2, fun h => by rw [hMF.accessible]; exact hl3 h, hl4⟩
  have hH2' := hH2 s'.mem _ _ hMF hSO' hDA
  have hqM : s'.mem.readLE 1007400 1 = 34 := by
    have hqo : Outside 1007400 1 (rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) := by
      simp only [outside_append, outside_cons, outside_nil]
      exact ⟨Outside.of_sub hrt3 (by omega) (by omega), by omega, trivial⟩
    rw [hMF.readLE _ _ hqo, hqbyte]
  have hqacc' : s'.mem.accessible 1007400 1 false = true := by rw [hMF.accessible]; exact hqacc
  janus_run calls [hc2]
  grab_last_const Janus.Contracts.CatBytesOut as hCB
  grab_last_const Janus.MemFrame as hF2
  have hq1 : strBytes s'.mem 1007400 1 = [34] := by
    simp only [strBytes, List.range_one, List.map_cons, List.map_nil]
    rw [Nat.add_zero, ← Janus.Arm64.Memory.readLE_one, hqM]
  rw [hq1, hl4] at hCB
  have hl0 := Janus.Arm64.Memory.readLE_lt s.mem z.toNat 8
  have hl1' := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 8) 8
  have hl2' := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 16) 8
  have hl3' := Janus.Arm64.Memory.readLE_lt s.mem (z.toNat + 24) 8
  simp only [Nat.reducePow] at hl0 hl1' hl2' hl3'
  generalize hv : s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8 = v at *
  have hvlt : v < 2 ^ 256 := by omega
  have hd78 : decLen v ≤ 78 := decLen_le_of_lt_pow _ 78 (by omega) (Nat.lt_of_lt_of_le hvlt (by decide))
  have hd1 := decLen_pos v
  have hbs : ([34] ++ (decBytes v ++ [34])) = marshalJSONBytes v := rfl
  have hbl : (marshalJSONBytes v).length = decLen v + 2 := marshalJSONBytes_length _
  rw [hbs] at hCB
  obtain ⟨hlen, -, -, hr2, hBH⟩ := hCB
  obtain ⟨hr2a, -⟩ := hr2 (by omega) (Or.inl rfl)
  have hrp := roundupsize_pos_small (marshalJSONBytes v).length (by omega) (by omega)
  have hBH' := hBH (by omega)
  have h2 := MemFrame.mono (rs' := rt ++ [(BitVec.toNat s.sp - 4688, BitVec.toNat s.sp + 8)]) hF2 (fun a n h => by
    simp only [outside_append, outside_cons] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, by omega, by omega, trivial⟩)
  exact ⟨hBH', hMF.trans h2 fun a n h => ⟨h, h⟩⟩

namespace Witness

open Fv256.ToyRuntimeArm64

def hA : Nat := 0x600000
def hB : Nat := 0x610000
def rtT : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 8)]

/-- readiness of the toy runtime: a two-byte string and both heap blocks writable -/
def Hw : RtReady := fun a _ _ view =>
  ((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, 1007400, 1, p, 2, 1007400, 1])) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true

def implAt : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := sbts2Words }, { name := "model-cb", base := cbAddr, words := cat4Words }]
def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem rtView_acc (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem byte_mod (b : BitVec 8) : b.toNat % 18446744073709551616 = b.toNat :=
  Nat.mod_eq_of_lt (by have := b.isLt; simp at this; omega)

theorem or_mul256 : ∀ a, a < 256 → ∀ b, b < 256 → (a % 18446744073709551616 ||| b * 256 % 18446744073709551616) = a + 256 * b := by
  decide +kernel

theorem byte_lt (b : BitVec 8) : b.toNat < 256 := by have := b.isLt; simpa using this

theorem model1 : RtContract (Extracted.program.link implAt) ssAddr rtT 4096 Hw
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  have hlen3 : (argWords s 3).length = 3 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 3 = [0, p, 2] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp⟩
    · have hp' : argWords s 3 = _ := hp
      rw [hp'] at hlen3; simp at hlen3
  have hargs : argWords s 3 = [0, p, 2] := hp
  simp [slicebytetostringSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 1).toNat 2 false = true := by
    have h := hs2 (by omega); rw [h2] at h; exact h
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
    simp only [byte_mod]
    refine MemFrame.trans (rs := rtIf true rtT ++ (calleeStack s 4096 3 ++ []))
      (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
      (MemFrame.of_writeLE _ _ (rs := rtIf true rtT ++ (calleeStack s 4096 3 ++ [])) (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)) ?_
    intro a n h; exact ⟨h, h⟩
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    simp only [byte_mod]
    refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · rw [← h1]
      simp [strBytes, List.range_succ, Arm64.Memory.writeLE]
    · right; right; right
      exact ⟨Nat.le_refl _, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩

theorem div256 (r k : Nat) (hr : r < 256) : (r + 256 * k) / 256 = k ∧ (r + 256 * k) % 256 = r := by
  omega

theorem byte4_plain (a b c : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    (a + 256 * (b + 256 * (c + 256 * a))) % 256 = a ∧
    (a + 256 * (b + 256 * (c + 256 * a))) / 256 % 256 = b ∧
    (a + 256 * (b + 256 * (c + 256 * a))) / 65536 % 256 = c ∧
    (a + 256 * (b + 256 * (c + 256 * a))) / 16777216 % 256 = a := by
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

theorem model2 : RtContract (Extracted.program.link implAt) cbAddr rtT 4096 Hw (concatbyteSpec 3) := by
  rw [linked_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
  have hlen7 : (argWords s 7).length = 7 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 7 = [0, 1007400, 1, p, 2, 1007400, 1] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hp' : argWords s 7 = _ := hp
      rw [hp'] at hlen7; simp at hlen7
    · exact ⟨p, hp⟩
  have hargs : argWords s 7 = [0, 1007400, 1, p, 2, 1007400, 1] := hp
  have hargs' : argWords s (concatbyteSpec 3).nargs = [0, 1007400, 1, p, 2, 1007400, 1] := hp
  rw [hargs'] at hstr hbuf
  simp [strPairs, StrsIn, arg] at hstr hbuf
  simp [concatbyteSpec, argWords, wordsFrom, arg] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  obtain ⟨⟨hq1, hq1a⟩, ⟨hp1, hp1a⟩, -⟩ := hstr
  have hqa : s.mem.accessible (s.regs 1).toNat 1 false = true := by rw [h1]; exact hq1a (by omega)
  have hqa5 : s.mem.accessible (s.regs 5).toNat 1 false = true := by rw [h5]; exact hq1a (by omega)
  have hpa : s.mem.accessible (s.regs 3).toNat 2 false = true := by rw [h3]; exact hp1a (by omega)
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
    simp only [byte_mod]
    exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h5, ← h1]
    simp only [byte_mod]
    have hb0 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 1)))
    have hb1 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3)))
    have hb2 := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3) + 1))
    have hsum : (BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) + BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) * 256 +
        BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3) + 1)) * 65536 + BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) * 16777216)
        % 18446744073709551616 = (BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) + BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) * 256 +
        BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3) + 1)) * 65536 + BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) * 16777216) :=
      Nat.mod_eq_of_lt (by omega)
    subst h3
    have hin : (BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) * 256 +
              BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3) + 1)) * 65536 +
            BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) * 16777216) % 18446744073709551616 =
        BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) * 256 +
              BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3) + 1)) * 65536 +
            BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) * 16777216 := Nat.mod_eq_of_lt (by omega)
    rw [hin]
    generalize ea : BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 1))) = a at *
    generalize eb : BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3))) = b at *
    generalize ec : BitVec.toNat (s.mem.bytes (BitVec.toNat (s.regs 3) + 1)) = c at *
    have hv : a + (b * 256 + c * 65536 + a * 16777216) = a + 256 * (b + 256 * (c + 256 * a)) := by omega
    rw [hv]
    have h4 := byte4_plain a b c hb0 hb1 hb2
    have hl : (strBytes s.mem (BitVec.toNat (s.regs 1)) 1 ++ (strBytes s.mem (BitVec.toNat (s.regs 3)) 2 ++ strBytes s.mem (BitVec.toNat (s.regs 1)) 1)).length = 4 := by simp [strBytes]
    have hr : roundupsize 4 true = 8 := by decide
    refine ⟨hl.symm, ?_, ?_, ?_, ?_⟩
    · intro h; rw [hl] at h; omega
    · intro _ h; exact absurd rfl h
    · intro _ _; exact ⟨by rw [hl, hr], (6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩
    · intro _
      refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
      · simp [strBytes, List.range_succ, Arm64.Memory.writeLE, ea, eb, ec]
        refine ⟨by omega, h4.2.1, h4.2.2.1, h4.2.2.2⟩
      · intro i hi
        simp [Arm64.Memory.writeLE]
        rw [if_pos (by omega)]
        have e : 6356996 + i - 6356992 = i + 4 := by omega
        rw [e]
        have hp2 : 256 ^ 4 ≤ 256 ^ (i + 4) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.div_eq_of_lt (by omega)]

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = zp then 10 else
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
    mem := ⟨bytes, [⟨sp0 - 4688, 4688 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 8, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide +kernel

theorem hz : val256 s0.mem arg.toNat = 10 := by
  unfold val256 s0 arg zp
  decide

theorem hdb : decBytes 10 = [49, 48] := by
  rw [decBytes_ge 10 (by omega)]
  simp [decBytes_lt 1 (by omega)]

set_option maxRecDepth 100000 in
theorem pre : (GuardOK s0 (688 + 80) ∧ StackOK s0 4688 8 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4688) (4688 + 8) rtT ∧ Outside 989280 256 rtT ∧ Outside 1002589 256 rtT ∧ Outside 1007400 32 rtT ∧ (∀ r ∈ rtT, 32 ≤ r.1) ∧
    Ptr32 s0.mem arg false ∧ (arg.toNat + 32 ≤ s0.sp.toNat - 4688 ∨ s0.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s0.regs 28).toNat + 16 + 8 ≤ s0.sp.toNat - 4688 ∨ s0.sp.toNat + 8 ≤ (s0.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s0.mem arg.toNat →
      Hw [0, s0.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 80 - 384) (rtView rtT s0.mem)) ∧
    (100 ≤ val256 s0.mem arg.toNat → val256 s0.mem arg.toNat < 2 ^ 64 →
      Hw [0, s0.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s0.mem arg.toNat)), decLen (val256 s0.mem arg.toNat)]
        (s0.regs 28).toNat (s0.sp.toNat - 80 - 384 - 96) (rtView rtT s0.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s0.mem M (rtT ++ [(s0.sp.toNat - 4688, s0.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s0.mem arg.toNat)) →
      DecAt rtT 989280 1002589 960826 p l →
      Hw [0, 1007400, 1, p, l, 1007400, 1] (s0.regs 28).toNat (s0.sp.toNat - 80) (rtView rtT M))) := by
  rw [hz]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded, ?_, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => absurd h (by decide), fun h _ => absurd h (by decide), ?_⟩
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT, hA, hB]; decide
  · intro M p l hMF hSO hDA
    rw [hdb] at hSO
    have hl : l = 2 := by have := hSO.1; simpa using this
    subst hl
    refine ⟨Or.inr ⟨p, rfl⟩, ?_, ?_⟩
    · rw [rtView_acc, hMF.accessible]; decide
    · rw [rtView_acc, hMF.accessible]; decide

/-- The preconditions, the `slicebytetostring` and `stringtoslicebyte` contracts (toy runtime blocks, readiness `Hw`) and the readiness
hypothesis for the second call are jointly satisfiable. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s (688 + 80) ∧ StackOK s 4688 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4688) (4688 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 1007400 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384 - 96) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [(s.sp.toNat - 4688, s.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l →
      H [0, 1007400, 1, p, l, 1007400, 1] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt M))) :=
  ⟨implAt, rtT, Hw, ret, s0, arg, model1, model2, by rw [linked_eq]; exact hret, by rw [linked_eq]; exact setup, pre⟩


/-! ### The large-value path (`z = 10^7`: eight digits, `FormatUint` path, both runtime calls made) -/

def rtT16 : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 16)]

theorem rtView_acc16 (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT16 m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

def Hw8 : RtReady := fun a _ _ view =>
  ((∃ p, a = [0, p, 8]) ∨ (∃ p, a = [0, 1007400, 1, p, 8, 1007400, 1])) ∧
    view.accessible hA 8 true = true ∧ view.accessible hB 16 true = true

open Fv256.ToyRuntimeArm64 in
def implAt8 : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := sbts8Words }, { name := "model-cb", base := cbAddr, words := cb8Words }]
def linked8 : Program := { Extracted.program with segments := Extracted.program.segments ++ implAt8 }
theorem linked_eq8 : Extracted.program.link implAt8 = linked8 := rfl

theorem copy8_bytes (m : Janus.Arm64.Memory) (a p : Nat) :
    strBytes (m.writeLE a 8 (m.readLE p 8)) a 8 = strBytes m p 8 := by
  apply strBytes_congr
  intro i hi
  have := Janus.Contracts.IfaceModel.bytes_writeLE_readLE m a p 8 i hi
  exact this

theorem cat10_bytes (m : Janus.Arm64.Memory) (q1 q2 p B : Nat) :
    strBytes ((((m.writeLE (B + 8) 8 0).writeLE B 1 (m.bytes q1).toNat).writeLE (B + 1) 8 (m.readLE p 8)).writeLE (B + 9) 1 (m.bytes q2).toNat) B 10
      = strBytes m q1 1 ++ (strBytes m p 8 ++ strBytes m q2 1) := by
  have hb : ∀ j, j < 8 → BitVec.ofNat 8 (m.readLE p 8 / 256 ^ j) = m.bytes (p + j) :=
    fun j hj => Janus.Contracts.IfaceModel.byte_of_readLE m 8 p j hj
  simp only [strBytes, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
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

theorem model1_8 : RtContract (Extracted.program.link implAt8) ssAddr rtT16 4096 Hw8
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  have hlen3 : (argWords s 3).length = 3 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 3 = [0, p, 8] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact ⟨p, hp⟩
    · have hp' : argWords s 3 = _ := hp
      rw [hp'] at hlen3; simp at hlen3
  have hargs : argWords s 3 = [0, p, 8] := hp
  simp [slicebytetostringSpec, argWords, wordsFrom] at hp hstr hbuf hdis
  simp only [hA, hB] at hA8 hB8
  obtain ⟨h0, h1, h2⟩ := hp
  obtain ⟨hs1, hs2⟩ := hstr
  have hacc2 : s.mem.accessible (s.regs 1).toNat 8 false = true := by
    have h := hs2 (by omega); rw [h2] at h; exact h
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true]
    exact MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT16, hA]) (by omega) (by omega)
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [h1, copy8_bytes]
    refine ⟨⟨trivial, ?_, rfl⟩, ?_⟩
    · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
    · right; right; right
      exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT16, hA], by omega, by omega⟩

theorem model2_8 : RtContract (Extracted.program.link implAt8) cbAddr rtT16 4096 Hw8 (concatbyteSpec 3) := by
  rw [linked_eq8]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw8, rtView_acc16] at ha
  obtain ⟨hshape, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
  have hlen7 : (argWords s 7).length = 7 := by simp [argWords, wordsFrom]
  obtain ⟨p, hp⟩ : ∃ p, argWords s 7 = [0, 1007400, 1, p, 8, 1007400, 1] := by
    rcases hshape with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hp' : argWords s 7 = _ := hp
      rw [hp'] at hlen7; simp at hlen7
    · exact ⟨p, hp⟩
  have hargs : argWords s 7 = [0, 1007400, 1, p, 8, 1007400, 1] := hp
  have hargs' : argWords s (concatbyteSpec 3).nargs = [0, 1007400, 1, p, 8, 1007400, 1] := hp
  rw [hargs'] at hstr hbuf
  simp [strPairs, StrsIn, arg] at hstr hbuf
  simp [concatbyteSpec, argWords, wordsFrom, arg] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hp
  obtain ⟨⟨hq1, hq1a⟩, ⟨hp1, hp1a⟩, -⟩ := hstr
  have hqa : s.mem.accessible (s.regs 1).toNat 1 false = true := by rw [h1]; exact hq1a (by omega)
  have hqa5 : s.mem.accessible (s.regs 5).toNat 1 false = true := by rw [h5]; exact hq1a (by omega)
  have hpa : s.mem.accessible (s.regs 3).toNat 8 false = true := by rw [h3]; exact hp1a (by omega)
  janus_run
  apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
  · rw [hargs]
    simp only [List.getElem?_cons_zero, Option.getD_some, ite_true, byte_mod]
    repeat' first
      | exact MemFrame.refl _ _
      | (refine MemFrame.writeLE ?_ _ (r := (6356992, 6357008)) (by simp [rtIf, rtT16, hB]) (by omega) (by omega))
  · rw [hargs]
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, byte_mod]
    rw [h5, h1, h3]
    have hc := cat10_bytes s.mem 1007400 1007400 p 6356992
    simp only [Nat.reduceAdd] at hc
    have hl : (strBytes s.mem 1007400 1 ++ (strBytes s.mem p 8 ++ strBytes s.mem 1007400 1)).length = 10 := by simp [strBytes]
    have hr : roundupsize 10 true = 16 := by decide
    refine ⟨hl.symm, fun h => by omega, fun _ h => absurd rfl h, fun _ _ => ⟨by rw [hl, hr], (6356992, 6357008), by simp [rtT16, hB], by omega, by omega⟩, fun _ => ?_⟩
    refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
    · exact hc
    · intro i hi
      simp only [Janus.Arm64.Memory.bytes_writeLE]
      have c1 : ¬ (6357001 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357001 + 1) := by omega
      have c2 : ¬ (6356993 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356993 + 8) := by omega
      have c3 : ¬ (6356992 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6356992 + 1) := by omega
      have c4 : (6357000 ≤ 6356992 + 10 + i ∧ 6356992 + 10 + i < 6357000 + 8) := by omega
      rw [if_neg c1, if_neg c2, if_neg c3, if_pos c4]
      simp


def bytes8 (a : Nat) : Byte :=
  if a = zp then 0x80 else if a = zp + 1 then 0x96 else if a = zp + 2 then 0x98 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def s08 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes8, [⟨sp0 - 4688, 4688 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨hA, 8, true⟩, ⟨hB, 16, true⟩] ++ dregs⟩ }

theorem hret8 : RetAddr linked8 ret := RetAddr.of_check (by decide)

theorem setup8 : CallSetup (linked8.withExit ret) Extracted.entry [arg] s08 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s08] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded8 : Extracted.program.DataLoaded s08.mem := by
  unfold Program.DataLoaded
  decide +kernel

theorem hz8 : val256 s08.mem arg.toNat = 10000000 := by
  unfold val256 s08 arg zp
  decide

theorem hdl8 : decLen 10000000 = 8 := by
  simp (disch := omega) [decLen_ge, decLen_lt]

set_option maxRecDepth 100000 in
theorem pre8 : (GuardOK s08 (688 + 80) ∧ StackOK s08 4688 8 ∧ Extracted.program.DataLoaded s08.mem ∧
    Outside (s08.sp.toNat - 4688) (4688 + 8) rtT16 ∧ Outside 989280 256 rtT16 ∧ Outside 1002589 256 rtT16 ∧ Outside 1007400 32 rtT16 ∧ (∀ r ∈ rtT16, 32 ≤ r.1) ∧
    Ptr32 s08.mem arg false ∧ (arg.toNat + 32 ≤ s08.sp.toNat - 4688 ∨ s08.sp.toNat + 8 ≤ arg.toNat) ∧
    ((s08.regs 28).toNat + 16 + 8 ≤ s08.sp.toNat - 4688 ∨ s08.sp.toNat + 8 ≤ (s08.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s08.mem arg.toNat →
      Hw8 [0, s08.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 80 - 384) (rtView rtT16 s08.mem)) ∧
    (100 ≤ val256 s08.mem arg.toNat → val256 s08.mem arg.toNat < 2 ^ 64 →
      Hw8 [0, s08.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s08.mem arg.toNat)), decLen (val256 s08.mem arg.toNat)]
        (s08.regs 28).toNat (s08.sp.toNat - 80 - 384 - 96) (rtView rtT16 s08.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s08.mem M (rtT16 ++ [(s08.sp.toNat - 4688, s08.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s08.mem arg.toNat)) →
      DecAt rtT16 989280 1002589 960826 p l →
      Hw8 [0, 1007400, 1, p, l, 1007400, 1] (s08.regs 28).toNat (s08.sp.toNat - 80) (rtView rtT16 M))) := by
  rw [hz8, hdl8]
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded8, ?_, ?_, ?_, ?_, ?_,
    ⟨by decide, by decide⟩, by decide, by decide, fun h => absurd h (by decide), fun _ _ => ⟨Or.inl ⟨_, rfl⟩, ?_, ?_⟩, ?_⟩
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB, outside_cons, outside_nil]; decide
  · simp only [rtT16, hA, hB]; decide
  · rw [rtView_acc16]; decide
  · rw [rtView_acc16]; decide
  · intro M p l hMF hSO hDA
    have hl : l = 8 := by
      have h := hSO.1
      have h8 : (decBytes 10000000).length = 8 := hdl8
      omega
    subst hl
    refine ⟨Or.inr ⟨p, rfl⟩, ?_, ?_⟩
    · rw [rtView_acc16, hMF.accessible]; decide
    · rw [rtView_acc16, hMF.accessible]; decide

/-- **Large-value witness**: `z = 10^7` (eight digits, `FormatUint` path): both runtime calls are made and the readiness hypothesis for the
second call is exercised on the string `Dec` returns. -/
theorem big : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    RtContract (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.link impl) cbAddr rt 4096 H (concatbyteSpec 3) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s (688 + 80) ∧ StackOK s 4688 8 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4688) (4688 + 8) rt ∧ Outside 989280 256 rt ∧ Outside 1002589 256 rt ∧ Outside 1007400 32 rt ∧ (∀ r ∈ rt, 32 ≤ r.1) ∧
    Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
    ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4688 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
    (2 ^ 64 ≤ val256 s.mem z.toNat →
      H [0, s.sp.toNat - 80 - 384 + 94 + (98 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384) (rtView rt s.mem)) ∧
    (100 ≤ val256 s.mem z.toNat → val256 s.mem z.toNat < 2 ^ 64 →
      H [0, s.sp.toNat - 80 - 384 - 32 + (24 - decLen (val256 s.mem z.toNat)), decLen (val256 s.mem z.toNat)]
        (s.regs 28).toNat (s.sp.toNat - 80 - 384 - 96) (rtView rt s.mem)) ∧
    (∀ (M : Janus.Arm64.Memory) (p l : Nat),
      MemFrame s.mem M (rt ++ [(s.sp.toNat - 4688, s.sp.toNat + 8)]) →
      StrOut M p l (decBytes (val256 s.mem z.toNat)) →
      DecAt rt 989280 1002589 960826 p l →
      H [0, 1007400, 1, p, l, 1007400, 1] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt M))) ∧
    100 ≤ val256 s.mem z.toNat :=
  ⟨implAt8, rtT16, Hw8, ret, s08, arg, model1_8, model2_8, by rw [linked_eq8]; exact hret8, by rw [linked_eq8]; exact setup8, pre8,
    by rw [hz8]; decide⟩

end Witness

end Fv256.Arm64.MarshalJSON
