import Extracted
import Fv256.Amd64.CallSites.Live
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.HexSpec

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Fv256.C Fv256.Hex

namespace Fv256.Amd64.Hex

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"

set_option maxRecDepth 100000 in
theorem and_ptr : ∀ n, n < 65 → 1 ≤ n →
    ((18446744073709551616 - (18446744073709551552 + n) % 18446744073709551616) % 18446744073709551616 &&&
      ((0#64 - (BitVec.ofNat 64 n + 2#64)).sshiftRight 63).toNat) = 64 - n := by
  decide

set_option maxRecDepth 100000 in
theorem nibB3 : ∀ b, b < 64 → BitVec.sshiftRight (BitVec.ofNat 64 b + 193#64 + ((BitVec.ofNat 64 b + 196#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((b + 196) / 4) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem nibB2 : ∀ b, b < 64 → BitVec.sshiftRight (BitVec.ofNat 64 b + 129#64 + ((BitVec.ofNat 64 b + 132#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((b + 132) / 4) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem nibB1 : ∀ b, b < 64 → BitVec.sshiftRight (BitVec.ofNat 64 b + 65#64 + ((BitVec.ofNat 64 b + 68#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((b + 68) / 4) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem nibB0 : ∀ b, b < 64 → BitVec.sshiftRight (BitVec.ofNat 64 b + 1#64 + ((BitVec.ofNat 64 b + 4#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((b + 4) / 4) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem nibZ : BitVec.sshiftRight (18446744073709551615#64 + 1#64 + ((18446744073709551615#64 + 4#64).sshiftRight 63 >>> 62) + 3#64) 2 = 0#64 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem siL : ∀ n, n < 65 → 1 ≤ n → (BitVec.ofNat 64 n + (BitVec.ofNat 64 n - 1#64).sshiftRight 63 >>> 60 - 1#64).sshiftRight 4 = BitVec.ofNat 64 ((n - 1) / 16) := by
  decide +kernel

theorem clz_b (x : Nat) (hx : x < 2 ^ 64) (h : x ≠ 0) : 63 - Janus.Arm64.clzNat 64 x = Spec.bitLen x - 1 := by
  have := Util.clz_bl 64 x hx
  have h1 : 1 ≤ Spec.bitLen x := by simp [Spec.bitLen, h]
  omega

theorem bl64 (x : Nat) (hx : x < 2 ^ 64) : Spec.bitLen x ≤ 64 := by
  by_cases h : x = 0
  · simp [Spec.bitLen, h]
  · have := Util.clz_bl 64 x hx; omega

theorem pro_frame (m : Memory) (r v : Nat) (h : 74 ≤ r) :
    MemFrame m (((((m.writeLE (r - 8) 8 v).writeLE (r - 74) 16 0).writeLE (r - 58) 16 0).writeLE (r - 42) 16 0).writeLE (r - 26) 16 0 |>.writeLE (r - 24) 16 0)
      [(r - 74, r)] :=
  (((((MemFrame.refl _ _).writeLE v (List.mem_singleton_self _) (by omega) (by omega)).writeLE 0 (List.mem_singleton_self _) (by omega) (by omega)).writeLE 0 (List.mem_singleton_self _) (by omega) (by omega)).writeLE 0 (List.mem_singleton_self _) (by omega) (by omega)).writeLE 0 (List.mem_singleton_self _) (by omega) (by omega) |>.writeLE 0 (List.mem_singleton_self _) (by omega) (by omega)

theorem pro_fp (m : Memory) (r v : Nat) (h : 74 ≤ r) (hv : v < 2 ^ 64) :
    ((((((m.writeLE (r - 8) 8 v).writeLE (r - 74) 16 0).writeLE (r - 58) 16 0).writeLE (r - 42) 16 0).writeLE (r - 26) 16 0).writeLE (r - 24) 16 0).readLE (r - 8) 8 = v := by
  repeat rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
  rw [Janus.Arm64.Memory.readLE_writeLE_self]
  simpa using Nat.mod_eq_of_lt hv

theorem nibL3 (x : Nat) : BitVec.sshiftRight (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 193#64 + ((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 196#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((63 - Janus.Arm64.clzNat 64 x + 196) / 4) := nibB3 _ (by omega)
theorem nibL2 (x : Nat) : BitVec.sshiftRight (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 129#64 + ((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 132#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((63 - Janus.Arm64.clzNat 64 x + 132) / 4) := nibB2 _ (by omega)
theorem nibL1 (x : Nat) : BitVec.sshiftRight (BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 65#64 + ((BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x) + 68#64).sshiftRight 63 >>> 62) + 3#64) 2 = BitVec.ofNat 64 ((63 - Janus.Arm64.clzNat 64 x + 68) / 4) := nibB1 _ (by omega)
theorem nibL0 (x : Nat) (k : BitVec 64) (hx : x < 18446744073709551616) :
    BitVec.sshiftRight ((if x = 0 then 18446744073709551615#64 else if x = 0 then k else BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x)) + 1#64 +
      (((if x = 0 then 18446744073709551615#64 else if x = 0 then k else BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 x)) + 4#64).sshiftRight 63 >>> 62) + 3#64) 2
    = BitVec.ofNat 64 ((Spec.bitLen x + 3) / 4) := by
  by_cases h : x = 0
  · simp only [h, if_true]; rw [nibZ]; simp [Spec.bitLen]
  · simp only [h, if_false]
    rw [nibB0 _ (by omega), clz_b x hx h]
    have := Util.clz_bl 64 x hx
    have h1 : 1 ≤ Spec.bitLen x := by simp [Spec.bitLen, h]
    congr 1; omega

theorem shr_nib (x r : Nat) (hx : x < 2 ^ 64) (hr : r ≤ 60) : ((BitVec.ofNat 64 x) >>> r).toNat % 16 = x / 2 ^ r % 16 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow]

theorem iter_vals_shr (x : Nat) (hx : x < 2 ^ 64) :
  [
    hexChar (((BitVec.ofNat 64 x) >>> 60).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 56).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 52).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 48).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 44).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 40).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 36).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 32).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 28).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 24).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 20).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 16).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 12).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 8).toNat % 16) % 256,
    hexChar (((BitVec.ofNat 64 x) >>> 4).toNat % 16) % 256,
    hexChar (x % 16) % 256]
  = (List.range 16).map (fun t => hexChar (x / 16 ^ (15 - t) % 16)) := by
  simp only [List.range, List.range.loop, List.map]
  rw [shr_nib x 60 hx (by omega)]
  rw [shr_nib x 56 hx (by omega)]
  rw [shr_nib x 52 hx (by omega)]
  rw [shr_nib x 48 hx (by omega)]
  rw [shr_nib x 44 hx (by omega)]
  rw [shr_nib x 40 hx (by omega)]
  rw [shr_nib x 36 hx (by omega)]
  rw [shr_nib x 32 hx (by omega)]
  rw [shr_nib x 28 hx (by omega)]
  rw [shr_nib x 24 hx (by omega)]
  rw [shr_nib x 20 hx (by omega)]
  rw [shr_nib x 16 hx (by omega)]
  rw [shr_nib x 12 hx (by omega)]
  rw [shr_nib x 8 hx (by omega)]
  rw [shr_nib x 4 hx (by omega)]
  have hm' : ∀ n, hexChar (n % 16) % 256 = hexChar (n % 16) := fun n =>
    Nat.mod_eq_of_lt (by have := hexChar_lt (n % 16) (Nat.mod_lt _ (by decide)); omega)
  simp [hm']

/-- The loop invariant (amd64): `k` limbs (indices `k-1 .. 0`) still to be written; state `S` at the loop head. -/
def HexL (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat) (s : State) (k : Nat) : Prop :=
  ∀ (S : State) (zW nib : Nat), zW ≤ 3 → 1 ≤ nib → nib ≤ 16 * (zW + 1) → 16 * zW < nib → k ≤ zW + 1 →
      hexDigits (s.mem.readLE z.toNat 32) nib →
      S.rip = BitVec.ofNat 64 (Extracted.entry + 0xec) → S.regs 0 = z → S.regs 2 = BitVec.ofNat 64 nib →
      S.regs 6 = BitVec.ofNat 64 k - 1#64 → S.regs 4 = s.regs 4 - 104#64 → S.regs 5 = s.regs 4 - 8#64 →
      S.regs 14 = s.regs 14 → S.xmm = s.xmm →
      MemFrame s.mem S.mem [((s.regs 4).toNat - 74, (s.regs 4).toNat)] →
      S.mem.regions = s.mem.regions →
      S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      (∀ p, 16 * (3 - zW) ≤ p → p < 16 * (4 - k) →
        S.mem.readLE ((s.regs 4).toNat - 74 + 2 + p) 1 = hexChar (dig (s.mem.readLE z.toNat 32) p)) →
      Reaches ((Extracted.program.link impl).withExit ret) S
        (IsReturn fun s' => ABIReturn s s' ∧
          HexOut (valueAt s z 32) s'.mem (s'.regs 0).toNat (s'.regs 3).toNat ∧
            MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem hexbase (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 8) true = true)
    (hsp : 4208 ≤ (s.regs 4).toNat) (hspa : (s.regs 4).toNat + 8 ≤ 2 ^ 48) (hal : (s.regs 4).toNat % 8 = 0)
    (hout : Outside ((s.regs 4).toNat - 4208) 4216 rt)
    (hH : ∀ n, hexDigits (s.mem.readLE z.toNat 32) n → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2] (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem)
    (hSt : s.mem.accessible 5142664 256 false = true)
    (hdt : (s.regs 4).toNat - 4208 + (4208 + 8) ≤ 5142664 ∨ 5142664 + 256 ≤ (s.regs 4).toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (5142664 + c) 1 = hexChar c) :
    HexL impl rt H z ret s 0 := by
  unfold HexL
  intro S zW nib hzW hn1 hn2 hn3 hk hdn hpc h0 h2 h6 h4 h5 h14 hx hfr hreg hfp hbuf
  have hnib64 : nib ≤ 64 := by omega
  have hA := and_ptr nib (by omega) hn1
  have hP : ((BitVec.toNat (s.regs 4) - 104 + ((18446744073709551616 - (18446744073709551552 + nib) % 18446744073709551616) % 18446744073709551616 &&&
                ((0#64 - (BitVec.ofNat 64 nib + 2#64)).sshiftRight 63).toNat)) % 18446744073709551616 + 30) % 18446744073709551616
      = BitVec.toNat (s.regs 4) - 74 + (64 - nib) := by
    rw [hA]; omega
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, trivial⟩ <;> omega
  have hHn : H [0, BitVec.toNat (s.regs 4) - 104 + (64 - nib) + 30, nib + 2]
      (BitVec.toNat (s.regs 14)) (BitVec.toNat (s.regs 4) - 112) (rtView rt S.mem) := by
    rw [show BitVec.toNat (s.regs 4) - 104 + (64 - nib) + 30 = BitVec.toNat (s.regs 4) - 112 + 38 + (64 - nib) by omega, hrv]
    exact hH nib hdn
  have haccP : s.mem.accessible (BitVec.toNat (s.regs 4) - 74 + (64 - nib)) (nib + 2) false = true :=
    Janus.Arm64.Memory.accessible_sub s.mem hw (Or.inl rfl) (by omega) (by omega)
  have hB0 : (18446744073709551616 - (18446744073709551552 + nib) % 18446744073709551616) % 18446744073709551616 = 64 - nib := by omega
  have hB1 : 18446744073709551616 - (18446744073709551551 + nib) = 65 - nib := by omega
  have hA' : (64 - nib &&& ((0#64 - (BitVec.ofNat 64 nib + 2#64)).sshiftRight 63).toNat) = 64 - nib := by
    have h := hA; rw [hB0] at h; exact h
  janus64_run [hP, hA', hA, hB0, hB1] until [Extracted.entry + 0xec, Extracted.entry + 0x3a8] calls [hc]
  case hq => exact hbr (by decide)
  janus64_run
  rename_i w9 w8 w7 w6 w5 w4 w3 w2 w1 w0 hLeft hR
  have e1 : BitVec.toNat (s.regs 4) - 104 + (64 - nib) + 30 = (BitVec.toNat (s.regs 4) - 74) + (64 - nib) := by omega
  have e2 : BitVec.toNat (s.regs 4) - 104 + (65 - nib) + 30 = (BitVec.toNat (s.regs 4) - 74) + (64 - nib + 1) := by omega
  simp only [e1, e2] at hLeft hR
  have hfr' : MemFrame s.mem S.mem (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]) :=
    MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]) hfr (fun a n h => by
      simp only [outside_append, outside_cons, outside_nil] at h ⊢
      obtain ⟨-, h2, -⟩ := h
      exact ⟨by omega, trivial⟩)
  have hmr : ((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8) ∈ rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  have hch : MemFrame s.mem (((S.mem.writeLE ((s.regs 4).toNat - 74 + (64 - nib)) 1 48).writeLE ((s.regs 4).toNat - 74 + (64 - nib + 1)) 1 120).writeLE
      ((s.regs 4).toNat - 112) 8 4929960) (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]) :=
    ((hfr'.writeLE _ hmr (by omega) (by omega)).writeLE _ hmr (by omega) (by omega)).writeLE _ hmr (by omega) (by omega)
  have hcall := MemFrame.mono (rs' := rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]) hLeft (fun a n h => by
    simp only [outside_append, outside_cons, outside_nil] at h ⊢
    obtain ⟨h1, h2, -⟩ := h
    exact ⟨h1, by omega, by omega, trivial⟩)
  refine ⟨by rw [hx], ⟨nib, hdn, ?_⟩, hch.trans hcall fun a n h => ⟨h, h⟩⟩
  show StrOut w2 w9.toNat w8.toNat _
  have hacc : ∀ a n, w2.accessible a n false = s.mem.accessible a n false := fun a n => by
    rw [hLeft.accessible]; simp only [Janus.Arm64.Memory.accessible_writeLE]; exact hfr.accessible a n false
  refine fin_strout _ _ _ _ _ _ _ _ ?hl hacc hR.1 ?_
  case hl => simp [hexStrBytes]
  exact hex_strbytes S.mem (BitVec.toNat (s.regs 4) - 74) nib _ zW hzW hn1 hn2 hdn
    (fun p h1 h2 => hbuf p h1 (by omega))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem hexstep (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 8) true = true)
    (hsp : 4208 ≤ (s.regs 4).toNat) (hspa : (s.regs 4).toNat + 8 ≤ 2 ^ 48) (hal : (s.regs 4).toNat % 8 = 0)
    (hout : Outside ((s.regs 4).toNat - 4208) 4216 rt)
    (hH : ∀ n, hexDigits (s.mem.readLE z.toNat 32) n → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2] (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem)
    (hSt : s.mem.accessible 5142664 256 false = true)
    (hdt : (s.regs 4).toNat - 4208 + (4208 + 8) ≤ 5142664 ∨ 5142664 + 256 ≤ (s.regs 4).toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (5142664 + c) 1 = hexChar c)
    (k : Nat) (ih : HexL impl rt H z ret s k) :
    HexL impl rt H z ret s (k + 1) := by
  unfold HexL at ih ⊢
  intro S zW nib hzW hn1 hn2 hn3 hk hdn hpc h0 h2 h6 h4 h5 h14 hx hfr hreg hfp hbuf
  have h6' : S.regs 6 = BitVec.ofNat 64 k := by
    rw [h6]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hk3 : k ≤ 3 := by omega
  have hmod : (18446744073709551616 - (18446744073709551612 + (k + 1)) % 18446744073709551616) % 18446744073709551616 = 3 - k := by omega
  have a0 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 32 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 2) := by omega
  have a1 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 33 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 3) := by omega
  have a2 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 34 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 4) := by omega
  have a3 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 35 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 5) := by omega
  have a4 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 36 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 6) := by omega
  have a5 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 37 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 7) := by omega
  have a6 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 38 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 8) := by omega
  have a7 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 39 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 9) := by omega
  have a8 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 40 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 10) := by omega
  have a9 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 41 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 11) := by omega
  have a10 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 42 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 12) := by omega
  have a11 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 43 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 13) := by omega
  have a12 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 44 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 14) := by omega
  have a13 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 45 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 15) := by omega
  have a14 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 46 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 16) := by omega
  have a15 : (s.regs 4).toNat - 104 + (3 - k) * 16 + 47 = ((s.regs 4).toNat - 74) + (16 * (3 - k) + 17) := by omega
  janus64_run until [Extracted.entry + 0xec, Extracted.entry + 0x362]
  · exact absurd (show (BitVec.ofNat 64 (k + 1) - 1#64).msb = true by janus_assumption) (by
      have : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      rw [this, BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega)
  · simp only [hmod, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]
    have hxl : s.mem.readLE (z.toNat + k * 8) 8 < 2 ^ 64 := by
      exact Util.readLE8_lt s.mem (z.toNat + k * 8)
    have e6 : BitVec.ofNat 64 (k + 1) - 2#64 = BitVec.ofNat 64 k - 1#64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine ih _ zW nib hzW hn1 hn2 hn3 (by omega) hdn rfl ?h0 ?h2 ?h6 ?h4 ?h5 ?h14 ?hx ?hfr ?hreg ?hfp ?hbuf
    case h0 => simp [setRegF_apply, h0]
    case h2 => simp [setRegF_apply, h2]
    case h6 => simp [setRegF_apply, e6]
    case h4 => simp [setRegF_apply, h4]
    case h5 => simp [setRegF_apply, h5]
    case h14 => simp [setRegF_apply, h14]
    case hx => exact hx
    case hfr =>
      dsimp only
      exact st16_frame ((s.regs 4).toNat - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfr ((s.regs 4).toNat - 74, (s.regs 4).toNat) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)
    case hreg =>
      dsimp only
      exact Eq.trans (st16_regions S.mem ((s.regs 4).toNat - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) hreg
    case hfp =>
      dsimp only
      exact Eq.trans (st16_out S.mem ((s.regs 4).toNat - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) hfp
    case hbuf =>
      intro p hp1 hp2
      dsimp only
      by_cases hlow : p < 16 * (3 - k)
      · exact Eq.trans (st16_out S.mem ((s.regs 4).toNat - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) (hbuf p hp1 (by omega))
      · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 16 ∧ p = 16 * (3 - k) + t := ⟨p - 16 * (3 - k), by omega, by omega⟩
        have hsel : (if k = 0 then s.mem.readLE z.toNat 8 else if k = 1 then s.mem.readLE (z.toNat + 8) 8
            else if k = 2 then s.mem.readLE (z.toNat + 16) 8 else s.mem.readLE (z.toNat + 24) 8) =
            s.mem.readLE (z.toNat + k * 8) 8 := by
          obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
          all_goals simp
        have hvl := Util.readLE_32 s.mem z.toNat
        have hz0 := Util.readLE8_lt s.mem z.toNat
        have hz1 := Util.readLE8_lt s.mem (z.toNat + 8)
        have hz2 := Util.readLE8_lt s.mem (z.toNat + 16)
        have hdg : dig (s.mem.readLE z.toNat 32) (16 * (3 - k) + t) =
            s.mem.readLE (z.toNat + k * 8) 8 / 16 ^ (15 - t) % 16 := by
          unfold dig
          rw [hvl, show 63 - (16 * (3 - k) + t) = 16 * k + (15 - t) by omega]
          rw [dig_limb _ _ _ _ k (15 - t) hz0 hz1 hz2 (by omega) (by omega)]
          rw [hsel]
        rw [hdg, show BitVec.toNat (s.regs 4) - 74 + 2 + (16 * (3 - k) + t) = BitVec.toNat (s.regs 4) - 74 + 16 * (3 - k) + 2 + t by omega]
        refine Eq.trans (st16_get S.mem (BitVec.toNat (s.regs 4) - 74) (16 * (3 - k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t ht) ?_
        rw [iter_vals_shr _ hxl]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht, Option.map_some, Option.getD_some]
        rw [Nat.pow_one]
        exact Nat.mod_eq_of_lt (hexChar_lt _ (Nat.mod_lt _ (by decide)))

set_option maxRecDepth 20000 in
theorem hexloop (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»))
    (s : State) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat)
    (hw : s.mem.accessible ((s.regs 4).toNat - 4208) (4208 + 8) true = true)
    (hsp : 4208 ≤ (s.regs 4).toNat) (hspa : (s.regs 4).toNat + 8 ≤ 2 ^ 48) (hal : (s.regs 4).toNat % 8 = 0)
    (hout : Outside ((s.regs 4).toNat - 4208) 4216 rt)
    (hH : ∀ n, hexDigits (s.mem.readLE z.toNat 32) n → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2] (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem)
    (hSt : s.mem.accessible 5142664 256 false = true)
    (hdt : (s.regs 4).toNat - 4208 + (4208 + 8) ≤ 5142664 ∨ 5142664 + 256 ≤ (s.regs 4).toNat - 4208)
    (htab : ∀ c, c < 16 → s.mem.readLE (5142664 + c) 1 = hexChar c) :
    ∀ k, HexL impl rt H z ret s k := by
  intro k
  induction k with
  | zero => exact hexbase impl rt H z ret hret hc s hr hz hz' hzd hw hsp hspa hal hout hH hd hSt hdt htab
  | succ k ih => exact hexstep impl rt H z ret hret hc s hr hz hz' hzd hw hsp hspa hal hout hH hd hSt hdt htab k ih

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem correctness (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hc : RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»)) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 4208 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.xmm 15 = 0 ∧
        Outside ((s.regs 4).toNat - 4208) 4216 rt ∧ Outside 5142664 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (∀ n, hexDigits (valueAt s z 32) n → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2]
          (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem)))
      (fun s s' => HexOut (valueAt s z 32) s'.mem (s'.regs 0).toNat (s'.regs 3).toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)])) := by
  rintro ret hret s hs ⟨hg, hw, hd, hx15, hout, hout2, hal, ⟨hzn, hza⟩, hzd, hgd, hH⟩
  janus64_intro hs
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hwb, hwn, hwa⟩ := hw
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal hout hzd hgd
  janus64_data hd [hwa]
  have htab : ∀ c, c < 16 → s.mem.readLE (5142664 + c) 1 = hexChar c := by
    intro c hc
    have hc16 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 := by omega
    rcases hc16 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [h_rodata _ _ (by decide)]; decide)
  have hloop := hexloop impl rt H z ret hret hc s h_ret hza hzn hzd hwa (by omega) (by omega) hal hout hH hd h_data0 h_ddisj0_0 htab
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
  have hb3 : s.mem.readLE (z.toNat + 24) 8 ≠ 0 → Spec.bitLen (s.mem.readLE z.toNat 32) = 192 + Spec.bitLen (s.mem.readLE (z.toNat + 24) 8) := by
    intro h; rw [Util.readLE_32, hbl]; simp [h]
  have hb2 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 ≠ 0 → Spec.bitLen (s.mem.readLE z.toNat 32) = 128 + Spec.bitLen (s.mem.readLE (z.toNat + 16) 8) := by
    intro h h'; rw [Util.readLE_32, hbl]; simp [h, h']
  have hb1 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 = 0 → s.mem.readLE (z.toNat + 8) 8 ≠ 0 → Spec.bitLen (s.mem.readLE z.toNat 32) = 64 + Spec.bitLen (s.mem.readLE (z.toNat + 8) 8) := by
    intro h h' h''; rw [Util.readLE_32, hbl]; simp [h, h', h'']
  have hb0 : s.mem.readLE (z.toNat + 24) 8 = 0 → s.mem.readLE (z.toNat + 16) 8 = 0 → s.mem.readLE (z.toNat + 8) 8 = 0 → Spec.bitLen (s.mem.readLE z.toNat 32) = Spec.bitLen (s.mem.readLE z.toNat 8) := by
    intro h h' h''; rw [Util.readLE_32, hbl]; simp [h, h', h'']
  have bl0 := bl64 _ x0
  have bl1 := bl64 _ x1
  have bl2 := bl64 _ x2
  have bl3 := bl64 _ x3
  obtain ⟨nib, hnib⟩ : ∃ n, n = max 1 ((Spec.bitLen (s.mem.readLE z.toNat 32) + 3) / 4) := ⟨_, rfl⟩
  obtain ⟨zW, hzW⟩ : ∃ w, w = (nib - 1) / 16 := ⟨_, rfl⟩
  have hdn : hexDigits (s.mem.readLE z.toNat 32) nib := nib_spec _ _ hnib
  have hnb : nib ≤ 64 := by omega
  have hn1 : 1 ≤ nib := by omega
  have hzW3 : zW ≤ 3 := by omega
  have hn2 : nib ≤ 16 * (zW + 1) := by omega
  have hn3 : 16 * zW < nib := by omega
  janus64_run until [Extracted.entry + 0xec]
  all_goals
    refine hloop (zW + 1) _ zW nib hzW3 hn1 hn2 hn3 (Nat.le_refl _) hdn rfl ?_ ?_ ?_ rfl rfl rfl rfl ?_ rfl ?_ ?_
    · simp [setRegF_apply, h_a0]
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, ite_true, nibL3, nibL2, nibL1, nibL0 _ _ x0] at hbr ⊢
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr ⊢
      omega
    · simp only [setRegF_apply, Nat.reduceEqDiff, ↓reduceIte, ite_true, nibL3, nibL2, nibL1, nibL0 _ _ x0] at hbr ⊢
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hbr
      try simp (disch := omega) only [siL]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega
    · exact pro_frame _ _ _ (by omega)
    · exact pro_fp _ _ _ (by omega) (BitVec.isLt _)
    · intro p h1 h2; omega

namespace Witness

open Janus.Contracts.SatAmd64
open Janus.Contracts.Sat (rtW HEAP)

/-- The readiness of the witness: the call is `slicebytetostring(nil, p, 3)` and the heap block is writable. -/
def H1 : RtReady := fun a _ sp v => arg a 0 = 0 ∧ arg a 2 = 3 ∧ v.accessible HEAP 3 true = true ∧ (HEAP + 3 ≤ sp - 4096 ∨ sp + 32 ≤ HEAP)

/-- `slicebytetostring(nil, p, 3)`: read the three bytes, copy them to the heap block, return `(HEAP, 3)`. -/
def copyCode : List Nat :=
  [0x44, 0x0F, 0xB6, 0x03, 0x44, 0x0F, 0xB6, 0x4B, 0x01, 0x44, 0x0F, 0xB6, 0x53, 0x02] ++ [0xBF] ++ le32 HEAP ++
  [0x44, 0x88, 0x07, 0x44, 0x88, 0x4F, 0x01, 0x44, 0x88, 0x57, 0x02] ++ [0xB8] ++ le32 HEAP ++ [0xBB, 3, 0, 0, 0, 0xC3]

def implAt : List Amd64.Segment := [{ name := "model", base := ssAddr, bytes := copyCode }]
def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAt }
theorem linked_eq : Extracted.program.link implAt = linked := rfl

theorem model : RtContract64 (Extracted.program.link implAt) ssAddr rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [linked_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, hpre, -, -, hH⟩
  have ha := ready_of rfl hH
  simp [Ready64, H1, arg, slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs] at hpre ha
  obtain ⟨ha0, ha2, hHeap, hHdis⟩ := ha
  obtain ⟨-, ⟨hsn, hsacc⟩, -⟩ := hpre
  rw [ha2] at hsn hsacc
  have hsacc' := hsacc (by omega)
  janus64_run
  have hargs : argWords64 s 3 = [(s.regs 0).toNat, (s.regs 3).toNat, (s.regs 1).toNat] := by
    simp [argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs]
  have hrt : ((HEAP, HEAP + 0x10000)) ∈ rtW := by simp [rtW, HEAP]
  apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf, setRegF_apply])
  · simp only [hargs]
    simp [ha0, rtIf]
    refine ((MemFrame.refl _ _).writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP])).writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP]) |>.writeLE _ (r := (HEAP, HEAP + 0x10000)) (by simp [rtW, HEAP]) (by simp [HEAP]) (by simp [HEAP])
  · simp only [hargs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    refine ⟨⟨ha2.symm, ?_, ?_⟩, ?_⟩
    · exact Janus.Arm64.Memory.accessible_sub s.mem h_num1 (Or.inl rfl) (by omega) (by omega)
    · rw [ha2]
      simp [Spec.strBytes, List.range_succ, Janus.Arm64.Memory.bytes_writeLE, HEAP]
    · simp [StrAt, ha0, ha2, InRanges, rtW, HEAP]

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then arg else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4208, 4208 + 8, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x100, false⟩, ⟨HEAP, 0x10000, true⟩] ++ dregs⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide +kernel

set_option maxRecDepth 100000 in
theorem pre : StackGuardOK s0 0 ∧ StackWritable s0 4208 8 ∧ Extracted.program.DataLoaded s0.mem ∧ s0.xmm 15 = 0 ∧
        Outside ((s0.regs 4).toNat - 4208) 4216 rtW ∧ Outside 5142664 256 rtW ∧
        (s0.regs 4).toNat % 8 = 0 ∧ Buffer s0 arg 32 false ∧
        (arg.toNat + 32 ≤ (s0.regs 4).toNat - 4208 ∨ (s0.regs 4).toNat + 8 ≤ arg.toNat) ∧
        ((s0.regs 14).toNat + 24 ≤ (s0.regs 4).toNat - 4208 ∨ (s0.regs 4).toNat + 8 ≤ (s0.regs 14).toNat + 16) ∧
        (∀ n, hexDigits (valueAt s0 arg 32) n → H1 [0, (s0.regs 4).toNat - 112 + 38 + (64 - n), n + 2]
          (s0.regs 14).toNat ((s0.regs 4).toNat - 112) (rtView rtW s0.mem)) := by
  have hz : s0.mem.readLE arg.toNat 32 = 0 := by
    unfold s0 arg zp
    decide
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, dataLoaded, by decide, ?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    fun n hn => ?_⟩
  · simp only [rtW, outside_cons, outside_nil]; decide
  · simp only [rtW, outside_cons, outside_nil]; decide
  · have h1 : n = 1 := by
      have := hn.2.1
      simp only [valueAt, hz] at this hn
      rcases hn with ⟨h1, h2, h3 | h3⟩
      · exact h3
      · simp at h3
    subst h1
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide

/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `slicebytetostring(nil, HEAP, 3)` at its entry, in the
caller's frame (`RSP = sp0 - 112`). -/
def csSb : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 HEAP else if i = 1 then BitVec.ofNat 64 3 else if i = 4 then BitVec.ofNat 64 (sp0 - 112) else s0.regs i }

theorem csSb_rip : csSb.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre64 rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  have hargs : argWords64 csSb 3 = [0, HEAP, 3] := by
    unfold argWords64 csSb; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show H1 (argWords64 csSb 3) (csSb.regs 14).toNat (csSb.regs 4).toNat (rtView rtW csSb.mem)
      rw [hargs]
      refine ⟨by decide, by decide, ?_, by decide⟩
      decide
    · trivial

/-- The precondition and the `slicebytetostring` contract are jointly satisfiable: a concrete call state (with a toy
`slicebytetostring` linked at its address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : Amd64.State) (z : BitVec 64),
    RtContract64 (Extracted.program.link impl) ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧
      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 4208 8 ∧ Extracted.program.DataLoaded s.mem ∧ s.xmm 15 = 0 ∧
        Outside ((s.regs 4).toNat - 4208) 4216 rt ∧ Outside 5142664 256 rt ∧
        (s.regs 4).toNat % 8 = 0 ∧ Buffer s z 32 false ∧
        (z.toNat + 32 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ z.toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 4208 ∨ (s.regs 4).toNat + 8 ≤ (s.regs 14).toNat + 16) ∧
        (∀ n, hexDigits (valueAt s z 32) n → H [0, (s.regs 4).toNat - 112 + 38 + (64 - n), n + 2]
          (s.regs 14).toNat ((s.regs 4).toNat - 112) (rtView rt s.mem))) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ HexOut (valueAt s z 32) s'.mem (s'.regs 0).toNat (s'.regs 3).toNat ∧
        MemFrame s.mem s'.mem (rt ++ [((s.regs 4).toNat - 4208, (s.regs 4).toNat + 8)]) := by
  refine ⟨implAt, rtW, H1, ret, s0, arg, model, ⟨csSb, csSb_rip, csSb_pre⟩, ?w1, ?w2, pre,
    correctness implAt rtW H1 arg model ret ?w1 s0 ?w2 pre⟩
  case w1 => exact by rw [linked_eq]; exact hret
  case w2 => exact by rw [linked_eq]; exact setup

end Witness

end Fv256.Amd64.Hex
