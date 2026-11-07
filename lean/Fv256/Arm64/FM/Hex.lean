import Fv256.FmTac
import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.HexSpec

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Hex

namespace Fv256.Arm64.FM.Hex

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem and_ptr : ∀ n, n < 65 → 1 ≤ n →
    (18446744073709551616 - n - 18446744073709551552 &&& ((0#64 - (BitVec.ofNat 64 n + 2#64)).sshiftRight 63).toNat) = 64 - n := by
  decide

theorem sub_aux1 (n : Nat) (h : n ≤ 64) : 18446744073709551616 - n - 18446744073709551552 = 64 - n := by omega
theorem sub_aux2 (n : Nat) (h : n ≤ 64) : 18446744073709551616 - n - 18446744073709551551 = 64 - n + 1 := by omega

theorem pro_frame (m : Memory) (r ret v : Nat) (h : 120 ≤ r) :
    MemFrame m (((((((((((m.writeLE (r - 112) 8 ret).writeLE (r - 120) 8 v).writeLE (r - 74) 8 0).writeLE (r - 66) 8 0).writeLE (r - 58) 8 0).writeLE (r - 50) 8 0).writeLE (r - 42) 8 0).writeLE (r - 34) 8 0).writeLE (r - 26) 8 0).writeLE (r - 18) 8 0).writeLE (r - 16) 8 0)
      [(r - 120, r - 104), (r - 74, r - 8)] := by
  have h1 : (r - 120, r - 104) ∈ [(r - 120, r - 104), (r - 74, r - 8)] := by simp
  have h2 : (r - 74, r - 8) ∈ [(r - 120, r - 104), (r - 74, r - 8)] := by simp
  exact (((((((((((MemFrame.refl _ _).writeLE ret h1 (by omega) (by omega)).writeLE v h1 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)).writeLE 0 h2 (by omega) (by omega)

theorem pro_rd1 (m : Memory) (r ret v : Nat) (h : 120 ≤ r) (hr : ret < 2 ^ 64) :
    (((((((((((m.writeLE (r - 112) 8 ret).writeLE (r - 120) 8 v).writeLE (r - 74) 8 0).writeLE (r - 66) 8 0).writeLE (r - 58) 8 0).writeLE (r - 50) 8 0).writeLE (r - 42) 8 0).writeLE (r - 34) 8 0).writeLE (r - 26) 8 0).writeLE (r - 18) 8 0).writeLE (r - 16) 8 0).readLE (r - 112) 8 = ret := by
  repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  rw [Memory.readLE_writeLE_self]
  simpa using Nat.mod_eq_of_lt hr

theorem pro_rd2 (m : Memory) (r ret v : Nat) (h : 120 ≤ r) (hv : v < 2 ^ 64) :
    (((((((((((m.writeLE (r - 112) 8 ret).writeLE (r - 120) 8 v).writeLE (r - 74) 8 0).writeLE (r - 66) 8 0).writeLE (r - 58) 8 0).writeLE (r - 50) 8 0).writeLE (r - 42) 8 0).writeLE (r - 34) 8 0).writeLE (r - 26) 8 0).writeLE (r - 18) 8 0).writeLE (r - 16) 8 0).readLE (r - 120) 8 = v := by
  repeat rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  rw [Memory.readLE_writeLE_self]
  simpa using Nat.mod_eq_of_lt hv

theorem clz_b (x : Nat) (hx : x < 2 ^ 64) (h : x ≠ 0) : 63 - Janus.Arm64.clzNat 64 x = Spec.bitLen x - 1 := by
  have := Util.clz_bl 64 x hx
  have h1 : 1 ≤ Spec.bitLen x := by simp [Spec.bitLen, h]
  omega

theorem bl64 (x : Nat) (hx : x < 2 ^ 64) : Spec.bitLen x ≤ 64 := by
  by_cases h : x = 0
  · simp [Spec.bitLen, h]
  · have := Util.clz_bl 64 x hx; omega

set_option maxRecDepth 100000 in
theorem N0Eq : ∀ c, c ≤ 64 → (if (64#64 - BitVec.ofNat 64 c + ((if (64#64 - BitVec.ofNat 64 c + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 3#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 13835058055282163712#64 ||| (64#64 - BitVec.ofNat 64 c + ((if (64#64 - BitVec.ofNat 64 c + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 3#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = BitVec.ofNat 64 ((64 - c + 0 + 3) / 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem H0Eq : ∀ c, c ≤ 64 → ((if (64#64 - BitVec.ofNat 64 c + ((if (64#64 - BitVec.ofNat 64 c + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 3#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 13835058055282163712 ||| ((64#64 - BitVec.ofNat 64 c + ((if (64#64 - BitVec.ofNat 64 c + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 3#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2).toNat % 4611686018427387904 = 0 ↔ (64 - c + 0 + 3) / 4 = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem N1Eq : ∀ c, c ≤ 64 → (if (64#64 - BitVec.ofNat 64 c + 64#64 + ((if (64#64 - BitVec.ofNat 64 c + 67#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 67#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 13835058055282163712#64 ||| (64#64 - BitVec.ofNat 64 c + 64#64 + ((if (64#64 - BitVec.ofNat 64 c + 67#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 67#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = BitVec.ofNat 64 ((64 - c + 64 + 3) / 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem H1Eq : ∀ c, c ≤ 64 → ((if (64#64 - BitVec.ofNat 64 c + 64#64 + ((if (64#64 - BitVec.ofNat 64 c + 67#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 67#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 13835058055282163712 ||| ((64#64 - BitVec.ofNat 64 c + 64#64 + ((if (64#64 - BitVec.ofNat 64 c + 67#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 67#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2).toNat % 4611686018427387904 = 0 ↔ (64 - c + 64 + 3) / 4 = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem N2Eq : ∀ c, c ≤ 64 → (if (64#64 - BitVec.ofNat 64 c + 128#64 + ((if (64#64 - BitVec.ofNat 64 c + 131#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 131#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 13835058055282163712#64 ||| (64#64 - BitVec.ofNat 64 c + 128#64 + ((if (64#64 - BitVec.ofNat 64 c + 131#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 131#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = BitVec.ofNat 64 ((64 - c + 128 + 3) / 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem H2Eq : ∀ c, c ≤ 64 → ((if (64#64 - BitVec.ofNat 64 c + 128#64 + ((if (64#64 - BitVec.ofNat 64 c + 131#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 131#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 13835058055282163712 ||| ((64#64 - BitVec.ofNat 64 c + 128#64 + ((if (64#64 - BitVec.ofNat 64 c + 131#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 131#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2).toNat % 4611686018427387904 = 0 ↔ (64 - c + 128 + 3) / 4 = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem N3Eq : ∀ c, c ≤ 64 → (if (64#64 - BitVec.ofNat 64 c + 192#64 + ((if (64#64 - BitVec.ofNat 64 c + 195#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 195#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 13835058055282163712#64 ||| (64#64 - BitVec.ofNat 64 c + 192#64 + ((if (64#64 - BitVec.ofNat 64 c + 195#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 195#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2 &&& 18446744073709551615#64 &&& 4611686018427387903#64 = BitVec.ofNat 64 ((64 - c + 192 + 3) / 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem H3Eq : ∀ c, c ≤ 64 → ((if (64#64 - BitVec.ofNat 64 c + 192#64 + ((if (64#64 - BitVec.ofNat 64 c + 195#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 195#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64).toNat &&& 13835058055282163712 ||| ((64#64 - BitVec.ofNat 64 c + 192#64 + ((if (64#64 - BitVec.ofNat 64 c + 195#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (64#64 - BitVec.ofNat 64 c + 195#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 62 + 3#64).rotateRight 2).toNat % 4611686018427387904 = 0 ↔ (64 - c + 192 + 3) / 4 = 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem SIEq : ∀ n, n < 65 → 1 ≤ n → (if (BitVec.ofNat 64 n + ((if (BitVec.ofNat 64 n - 1#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (BitVec.ofNat 64 n - 1#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 60 - 1#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 17293822569102704640#64 ||| (BitVec.ofNat 64 n + ((if (BitVec.ofNat 64 n - 1#64).getLsbD 63 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551614#64 ||| (BitVec.ofNat 64 n - 1#64).rotateRight 63 &&& 18446744073709551615#64 &&& 1#64) >>> 60 - 1#64).rotateRight 4 &&& 18446744073709551615#64 &&& 1152921504606846975#64 = BitVec.ofNat 64 ((n - 1) / 16) := by
  decide +kernel

def HexL (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State) (k : Nat) : Prop :=
  ∀ (S : State) (zW nib : Nat), zW ≤ 3 → 1 ≤ nib → nib ≤ 16 * (zW + 1) → 16 * zW < nib → k ≤ zW + 1 →
      hexDigits (val256 s.mem z.toNat) nib →
      S.pc = BitVec.ofNat 64 ((Extracted.entry + 0x1c60) + 0xd0) → S.regs 0 = z → S.regs 3 = s.sp - 74#64 →
      S.regs 4 = BitVec.ofNat 64 nib → S.regs 5 = BitVec.ofNat 64 k - 1#64 → S.sp = s.sp - 112#64 →
      S.regs 28 = s.regs 28 → S.regs 29 = s.sp - 120#64 → S.regs 30 = s.regs 30 → S.regs 18 = s.regs 18 →
      MemFrame s.mem S.mem [(s.sp.toNat - 120, s.sp.toNat - 104), (s.sp.toNat - 74, s.sp.toNat - 8)] →
      S.mem.regions = s.mem.regions →
      S.mem.readLE (s.sp.toNat - 112) 8 = ret → S.mem.readLE (s.sp.toNat - 120) 8 = (s.regs 29).toNat →
      (∀ p, 16 * (3 - zW) ≤ p → p < 16 * (4 - k) →
        S.mem.readLE (s.sp.toNat - 74 + 2 + p) 1 = hexChar (dig (val256 s.mem z.toNat) p)) →
      Reaches (((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧ HexOut (val256 s.mem z.toNat) s'.mem (s'.regs 0).toNat (s'.regs 1).toNat ∧ InRanges (s'.regs 0).toNat (s'.regs 1).toNat rt ∧
          MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4208, s.sp.toNat - 8)]))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 16000000 in
theorem hexbase (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ret)
    (hc : RtContract ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hlr : s.regs 30 = BitVec.ofNat 64 ret) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hdis : z.toNat + 32 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 8 ≤ z.toNat)
    (hsp : 4208 ≤ s.sp.toNat) (hspa : s.sp.toNat + 8 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4208) (4208 + 8) true = true)
    (hout : Outside (s.sp.toNat - 4208) (4208 + 8) rt)
    (hH : ∀ n, hexDigits (val256 s.mem z.toNat) n → H [0, s.sp.toNat - 112 + 38 + (64 - n), n + 2] (s.regs 28).toNat (s.sp.toNat - 112) (rtView rt s.mem))
    (hSt : s.mem.accessible 968614 256 false = true)
    (hdt : s.sp.toNat - 4208 + (4208 + 8) ≤ 968614 ∨ 968614 + 256 ≤ s.sp.toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (968614 + c) 1 = hexChar c) :
    HexL impl rt H z ret s 0 := by
  unfold HexL
  intro S zW nib hzW hn1 hn2 hn3 hk hdn hpc h0 h3 h4 h5 hsp' h28 h29 h30 h18 hfr hreg hlr' hfp hbuf
  have hsb : (BitVec.ofNat 64 0 - 1#64).getLsbD 63 = true := by decide
  have hnib64 : nib ≤ 64 := by omega
  have hA := and_ptr nib (by omega) hn1
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  have hHn : H [0, BitVec.toNat s.sp - 74 + (18446744073709551616 - nib - 18446744073709551552 &&&
      ((0#64 - (BitVec.ofNat 64 nib + 2#64)).sshiftRight 63).toNat), nib + 2]
      (BitVec.toNat (s.regs 28)) (BitVec.toNat s.sp - 112) (rtView rt S.mem) := by
    rw [hA, show BitVec.toNat s.sp - 74 + (64 - nib) = BitVec.toNat s.sp - 112 + 38 + (64 - nib) by omega, hrv]
    exact hH nib hdn
  have haccP : 0 < nib + 2 → s.mem.accessible (BitVec.toNat s.sp - 74 + (18446744073709551616 - nib - 18446744073709551552 &&&
      ((0#64 - (BitVec.ofNat 64 nib + 2#64)).sshiftRight 63).toNat)) (nib + 2) false = true := by
    intro _
    rw [hA]
    exact Memory.accessible_sub s.mem hw (Or.inl rfl) (by omega) (by omega)
  have hF : False → Disjoint (BitVec.toNat s.sp - 74 + (18446744073709551616 - nib - 18446744073709551552 &&&
      ((0#64 - (BitVec.ofNat 64 nib + 2#64)).sshiftRight 63).toNat)) (nib + 2) 0 32 := fun h => h.elim
  janus_run until [(Extracted.entry + 0x1c60) + 0xd4, (Extracted.entry + 0x1c60) + 0x304] calls [hc]
  all_goals
    simp only [hlr', hfp, ← hlr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    janus_run
    rename_i w8 w7 w6 w5 w4 w3 w2 w1 w0 hLeft hR
    have e1 := sub_aux1 nib hnib64
    have e2 := sub_aux2 nib hnib64
    rw [e1, e2] at hLeft
    rw [hA, e1, e2] at hR
    have hfr' : MemFrame s.mem S.mem (rt ++ [(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)]) :=
      MemFrame.mono (rs' := rt ++ [(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)]) hfr (fun a n h => by
        simp only [outside_append, outside_cons, outside_nil] at h ⊢
        obtain ⟨-, h2, -⟩ := h
        exact ⟨by omega, by omega, trivial⟩)
    have hmr : (BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8) ∈ rt ++ [(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)] :=
      List.mem_append_right _ (List.mem_singleton_self _)
    have hch : MemFrame s.mem ((S.mem.writeLE (BitVec.toNat s.sp - 74 + (64 - nib)) 1 48).writeLE
        (BitVec.toNat s.sp - 74 + (64 - nib + 1)) 1 120) (rt ++ [(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)]) :=
      (hfr'.writeLE _ hmr (by omega) (by omega)).writeLE _ hmr (by omega) (by omega)
    have hcall := MemFrame.mono (rs' := rt ++ [(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)]) hLeft (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨h1, h2, -⟩ := h
      exact ⟨h1, by omega, by omega, trivial⟩)
    refine ⟨⟨nib, ?_, ?_⟩, ?_, hch.trans hcall fun a n h => ⟨h, h⟩⟩
    · rw [Spec.val256_limbs] at hdn; exact hdn
    · show StrOut w2 w8.toNat w7.toNat _
      have hacc : ∀ a n, w2.accessible a n false = s.mem.accessible a n false := fun a n => by
        rw [hLeft.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hfr.accessible a n false
      refine fin_strout _ _ _ _ _ _ _ _ ?hl hacc hR.1 ?_
      case hl => simp [hexStrBytes]
      rw [← Spec.val256_limbs s.mem z.toNat]
      exact hex_strbytes S.mem (BitVec.toNat s.sp - 74) nib _ zW hzW hn1 hn2 hdn
        (fun p h1 h2 => hbuf p h1 (by omega))
    · have hl : BitVec.toNat w7 = nib + 2 := by have := hR.1.1; simpa [Spec.strBytes] using this
      rcases hR.2 with h | ⟨h, -⟩ | ⟨h, hb, -⟩ | ⟨-, -, hin⟩
      · omega
      · omega
      · exact absurd rfl hb
      · exact hin

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem hexstep (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ret)
    (hc : RtContract ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hlr : s.regs 30 = BitVec.ofNat 64 ret) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hdis : z.toNat + 32 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 8 ≤ z.toNat)
    (hsp : 4208 ≤ s.sp.toNat) (hspa : s.sp.toNat + 8 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4208) (4208 + 8) true = true)
    (hout : Outside (s.sp.toNat - 4208) (4208 + 8) rt)
    (hH : ∀ n, hexDigits (val256 s.mem z.toNat) n → H [0, s.sp.toNat - 112 + 38 + (64 - n), n + 2] (s.regs 28).toNat (s.sp.toNat - 112) (rtView rt s.mem))
    (hSt : s.mem.accessible 968614 256 false = true)
    (hdt : s.sp.toNat - 4208 + (4208 + 8) ≤ 968614 ∨ 968614 + 256 ≤ s.sp.toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (968614 + c) 1 = hexChar c) (k : Nat) (ih : HexL impl rt H z ret s k) :
    HexL impl rt H z ret s (k + 1) := by
  unfold HexL at ih ⊢
  intro S zW nib hzW hn1 hn2 hn3 hk hdn hpc h0 h3 h4 h5 hsp' h28 h29 h30 h18 hfr hreg hlr' hfp hbuf
  have h5' : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hsb : ¬ ((BitVec.ofNat 64 (k + 1) - 1#64).getLsbD 63 == true) = true := by
    rw [h5', BitVec.getLsbD_ofNat]
    have : k.testBit 63 = false := Nat.testBit_lt_two_pow (by omega)
    simp [this]
  janus_run until [(Extracted.entry + 0x1c60) + 0xd0, (Extracted.entry + 0x1c60) + 0x2b4]
  · exact absurd ‹_› hsb
  · have hx : s.mem.readLE (z.toNat + 8 * k) 8 < 2 ^ 64 := by
      have := Memory.readLE_lt s.mem (z.toNat + 8 * k) 8
      simpa using this
    have hk3 : k ≤ 3 := by omega
    have e5 : BitVec.ofNat 64 (k + 1) - 2#64 = BitVec.ofNat 64 k - 1#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hmod : (18446744073709551616 - k + 3) % 18446744073709551616 = 3 - k := by omega
    simp only [hmod]
    refine ih _ zW nib hzW hn1 hn2 hn3 (by omega) hdn rfl ?h0 ?h3 ?h4 ?h5 rfl ?h28 ?h29 ?h30 ?h18 ?hfr ?hreg ?hlr ?hfp ?hbuf
    case h0 => simp [setReg_apply, h0]
    case h3 => simp [setReg_apply, h3]
    case h4 => simp [setReg_apply, h4]
    case h5 => simp [setReg_apply, e5]
    case h28 => simp [setReg_apply, h28]
    case h29 => simp [setReg_apply, h29]
    case h30 => simp [setReg_apply, h30]
    case h18 => simp [setReg_apply, h18]
    case hfr =>
      dsimp only
      exact st16_frame (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfr (BitVec.toNat s.sp - 74, BitVec.toNat s.sp - 8) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)
    case hreg =>
      dsimp only
      exact Eq.trans (st16_regions S.mem (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hreg
    case hlr =>
      dsimp only
      exact Eq.trans (st16_out S.mem (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) hlr'
    case hfp =>
      dsimp only
      exact Eq.trans (st16_out S.mem (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) hfp
    case hbuf =>
      intro p hp1 hp2
      dsimp only
      by_cases hlow : p < 16 * (3 - k)
      · exact Eq.trans (st16_out S.mem (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) (hbuf p hp1 (by omega))
      · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 16 ∧ p = 16 * (3 - k) + t := ⟨p - 16 * (3 - k), by omega, by omega⟩
        have hsel : (if k = 0 then s.mem.readLE z.toNat 8 else if k = 1 then s.mem.readLE (z.toNat + 8) 8
            else if k = 2 then s.mem.readLE (z.toNat + 16) 8 else s.mem.readLE (z.toNat + 24) 8) =
            s.mem.readLE (z.toNat + 8 * k) 8 := by
          obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          all_goals simp
        have hvl := Spec.val256_limbs s.mem z.toNat
        have hz0 := Memory.readLE_lt s.mem z.toNat 8
        have hz1 := Memory.readLE_lt s.mem (z.toNat + 8) 8
        have hz2 := Memory.readLE_lt s.mem (z.toNat + 16) 8
        have hdg : dig (val256 s.mem z.toNat) (16 * (3 - k) + t) =
            s.mem.readLE (z.toNat + 8 * k) 8 / 16 ^ (15 - t) % 16 := by
          unfold dig
          rw [hvl, show 63 - (16 * (3 - k) + t) = 16 * k + (15 - t) by omega]
          rw [dig_limb _ _ _ _ k (15 - t) (by simpa using hz0) (by simpa using hz1) (by simpa using hz2) (by omega) (by omega)]
          rw [hsel]
        rw [hdg, show BitVec.toNat s.sp - 74 + 2 + (16 * (3 - k) + t) = BitVec.toNat s.sp - 74 + 16 * (3 - k) + 2 + t by omega]
        refine Eq.trans (st16_get S.mem (BitVec.toNat s.sp - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ht) ?_
        rw [iter_vals _ hx]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some, Option.getD_some]
        rw [Nat.pow_one]
        exact Nat.mod_eq_of_lt (hexChar_lt _ (Nat.mod_lt _ (by decide)))


set_option maxRecDepth 20000 in
theorem hexloop (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ret)
    (hc : RtContract ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hlr : s.regs 30 = BitVec.ofNat 64 ret) (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hdis : z.toNat + 32 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 8 ≤ z.toNat)
    (hsp : 4208 ≤ s.sp.toNat) (hspa : s.sp.toNat + 8 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0)
    (hw : s.mem.accessible (s.sp.toNat - 4208) (4208 + 8) true = true)
    (hout : Outside (s.sp.toNat - 4208) (4208 + 8) rt)
    (hH : ∀ n, hexDigits (val256 s.mem z.toNat) n → H [0, s.sp.toNat - 112 + 38 + (64 - n), n + 2] (s.regs 28).toNat (s.sp.toNat - 112) (rtView rt s.mem))
    (hSt : s.mem.accessible 968614 256 false = true)
    (hdt : s.sp.toNat - 4208 + (4208 + 8) ≤ 968614 ∨ 968614 + 256 ≤ s.sp.toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (968614 + c) 1 = hexChar c) :
    ∀ k, HexL impl rt H z ret s k := by
  intro k
  induction k with
  | zero => exact hexbase impl rt H z ret hret hc s hlr hg1 hz hz' hdis hsp hspa hal hw hout hH hSt hdt htab
  | succ k ih => exact hexstep impl rt H z ret hret hc s hlr hg1 hz hz' hdis hsp hspa hal hw hout hH hSt hdt htab k ih


set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures ((Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl) (Extracted.entry + 0x1c60) [z]
      (fun s => GuardOK s 0 ∧ StackOK s 4208 8 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4208) (4208 + 8) rt ∧ Outside 968614 256 rt ∧
        Ptr32 s.mem z false ∧ (z.toNat + 32 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 8 ≤ z.toNat) ∧
        ((s.regs 28).toNat + 16 + 8 ≤ s.sp.toNat - 4208 ∨ s.sp.toNat + 8 ≤ (s.regs 28).toNat + 16) ∧
        (∀ n, hexDigits (val256 s.mem z.toNat) n → H [0, s.sp.toNat - 112 + 38 + (64 - n), n + 2]
          (s.regs 28).toNat (s.sp.toNat - 112) (rtView rt s.mem)))
      (fun s s' => HexOut (val256 s.mem z.toNat) s'.mem (s'.regs 0).toNat (s'.regs 1).toNat ∧ InRanges (s'.regs 0).toNat (s'.regs 1).toNat rt ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4208, s.sp.toNat - 8)])) := by
  rintro ret hret s hs ⟨hg, hst, hd, hout, hout2, ⟨hza, hzn⟩, hzd, hgd, hH⟩
  janus_intro hs
  obtain ⟨hg1, hg2, hg3⟩ := hg
  obtain ⟨hal, hsp, hspa, hwa⟩ := hst
  janus_data hd [hwa]
  fm_clear_ddisj 7
  have htab : ∀ c, c < 16 → s.mem.readLE (968614 + c) 1 = hexChar c := by
    intro c hc
    have hc16 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 := by omega
    rcases hc16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [h_rodata _ _ (by decide)]; decide)
  have hloop := hexloop impl rt H z ret hret hc s h_lr hg1 hza hzn hzd hsp hspa hal hwa hout hH h_data7 h_ddisj0_7 htab
  have x0 := Util.readLE8_lt s.mem z.toNat
  have x1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have x2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have x3 := Util.readLE8_lt s.mem (z.toNat + 24)
  have c0 := Util.clz_bl 64 _ x0
  have c1 := Util.clz_bl 64 _ x1
  have c2 := Util.clz_bl 64 _ x2
  have c3 := Util.clz_bl 64 _ x3
  have hbl := Util.bl_4 _ _ _ (s.mem.readLE (z.toNat + 24) 8) x0 x1 x2
  have n0 : s.mem.readLE z.toNat 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE z.toNat 8) := fun h => (by simp [Spec.bitLen, h])
  have n1 : s.mem.readLE (z.toNat + 8) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) := fun h => (by simp [Spec.bitLen, h])
  have n2 : s.mem.readLE (z.toNat + 16) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) := fun h => (by simp [Spec.bitLen, h])
  have n3 : s.mem.readLE (z.toNat + 24) 8 ≠ 0 → 1 ≤ Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) := fun h => (by simp [Spec.bitLen, h])
  have z0 : s.mem.readLE z.toNat 8 = 0 → Spec.bitLen (s.mem.readLE z.toNat 8) = 0 := fun h => (by simp [Spec.bitLen, h])
  have hv32 : val256 s.mem z.toNat = s.mem.readLE z.toNat 32 := rfl
  have hb3 : s.mem.readLE (z.toNat + 24) 8 ≠ 0 → Spec.bitLen (val256 s.mem z.toNat) = 192 + Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) := by
    intro h; rw [hv32, Util.readLE_32, hbl]; simp [h]
  have hb2 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 ≠ 0 → Spec.bitLen (val256 s.mem z.toNat) = 128 + Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) := by
    intro h h'; rw [hv32, Util.readLE_32, hbl]; simp [h, h']
  have hb1 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 = 0 → s.mem.readLE (z.toNat + 8) 8 ≠ 0 → Spec.bitLen (val256 s.mem z.toNat) = 64 + Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) := by
    intro h h' h''; rw [hv32, Util.readLE_32, hbl]; simp [h, h', h'']
  have hb0 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 = 0 → s.mem.readLE (z.toNat + 8) 8 = 0 → Spec.bitLen (val256 s.mem z.toNat) = Spec.bitLen (s.mem.readLE z.toNat 8) := by
    intro h h' h''; rw [hv32, Util.readLE_32, hbl]; simp [h, h', h'']
  have bl0 := bl64 _ x0
  have bl1 := bl64 _ x1
  have bl2 := bl64 _ x2
  have bl3 := bl64 _ x3
  obtain ⟨nib, hnib⟩ : ∃ n, n = max 1 ((Spec.bitLen (val256 s.mem z.toNat) + 3) / 4) := ⟨_, rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ w, w = (nib - 1) / 16 := ⟨_, rfl⟩
  have hdn : hexDigits (val256 s.mem z.toNat) nib := nib_spec _ _ hnib
  have hnb : nib ≤ 64 := by omega
  have hn1 : 1 ≤ nib := by omega
  have hzW3 : zW ≤ 3 := by omega
  have hn2 : nib ≤ 16 * (zW + 1) := by omega
  have hn3 : 16 * zW < nib := by omega
  have hret48 := hret.user
  have hr29 := (s.regs 29).isLt
  janus_run until [(Extracted.entry + 0x1c60) + 0xd0]
  all_goals
    refine hloop (zW + 1) _ zW nib hzW3 hn1 hn2 hn3 (Nat.le_refl _) hdn rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [setReg_apply, h_x0]
    · simp [setReg_apply]
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, ite_true]
      simp (disch := omega) only [N0Eq, N1Eq, N2Eq, N3Eq, H0Eq, H1Eq, H2Eq, H3Eq] at hbr ⊢
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, ite_true]
      simp (disch := omega) only [N0Eq, N1Eq, N2Eq, N3Eq, H0Eq, H1Eq, H2Eq, H3Eq] at hbr ⊢
      try simp (disch := omega) only [SIEq]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · rfl
    · simp [setReg_apply]
    · simp [setReg_apply]
    · simp [setReg_apply, h_lr]
    · simp [setReg_apply]
    · exact pro_frame _ _ _ _ (by omega)
    · rfl
    · exact pro_rd1 _ _ _ _ (by omega) (by omega)
    · exact pro_rd2 _ _ _ _ (by omega) (by omega)
    · intro p h1 h2; omega



end Fv256.Arm64.FM.Hex
