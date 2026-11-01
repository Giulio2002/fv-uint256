import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas
import Fv256.SumC64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Fv256.C

namespace Fv256.Amd64.SetFromHexLoops

abbrev fh : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).fromHex"
abbrev innerHead : Nat := fh + 0xf0

/-- postcondition of the digit loop (relative to the entry state `s` of `fromHex`) -/
def LoopQ (s : State) (z hp len : BitVec 64) (s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
  Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
    ((s.regs 4).toNat - 8, (s.regs 4).toNat)] ∧
  ((s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ allHex (bytesAt s.mem hp.toNat) 2 len.toNat ∧
      ∀ j, j < 4 → s'.mem.readLE (z.toNat + 8 * j) 8 = hexLimb (bytesAt s.mem hp.toNat) len.toNat j) ∨
   (s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE 5987136 8) ∧ s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE 5987144 8) ∧
      ¬ allHex (bytesAt s.mem hp.toNat) 2 len.toNat))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem loop (impl : List Janus.Segment) (s : State) (z hp len : BitVec 64) (hL : 3 ≤ len.toNat) (hL2 : len.toNat ≤ 66)
    (hz' : z.toNat + 32 ≤ 2 ^ 48) (hs' : hp.toNat + len.toNat ≤ 2 ^ 48)
    (hsa : s.mem.accessible hp.toNat len.toNat false = true)
    (hdz : z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat)
    (hdst : hp.toNat + len.toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat)
    (hdzs : z.toNat + 32 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ z.toNat)
    (hzt : z.toNat + 32 ≤ 5175774 ∨ 5175774 + 256 ≤ z.toNat)
    (hgz : z.toNat + 32 ≤ 5987120 ∨ 5987216 ≤ z.toNat)
    (hgs : (s.regs 4).toNat + 24 ≤ 5987120 ∨ 5987216 ≤ (s.regs 4).toNat - 8)
    (hsp : 8 ≤ (s.regs 4).toNat) (hspa : (s.regs 4).toNat + 24 ≤ 2 ^ 48)
    (hretlt : s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) :
    ∀ n (S : State) (i e0 e1 ri : Nat), n = 17 * (3 - i) + (e0 - ri) → i ≤ 3 →
      e0 = hexEnd len.toNat i → e1 = hexEnd len.toNat (i + 1) → e1 ≤ e0 → e0 ≤ len.toNat → 2 ≤ e1 → e0 ≤ e1 + 16 →
      e1 ≤ ri → ri ≤ e0 →
      S.rip = BitVec.ofNat 64 innerHead → S.regs 0 = z → S.regs 3 = hp → S.regs 2 = len →
      S.regs 6 = BitVec.ofNat 64 i → S.regs 1 = BitVec.ofNat 64 e0 →
      S.regs 8 = BitVec.ofNat 64 e1 → S.regs 7 = BitVec.ofNat 64 ri →
      S.regs 4 = s.regs 4 - 8#64 → S.regs 5 = s.regs 4 - 8#64 → S.regs 14 = s.regs 14 → S.xmm 15 = s.xmm 15 →
      S.df = s.df → S.fsBase = s.fsBase →
      allHex (bytesAt s.mem hp.toNat) e0 len.toNat →
      allHex (bytesAt s.mem hp.toNat) e1 ri →
      (∀ j, j < 4 → S.mem.readLE (z.toNat + 8 * j) 8 =
        if j < i then hexLimb (bytesAt s.mem hp.toNat) len.toNat j
        else if j = i then hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1)
        else 0) →
      Janus.MemFrame s.mem S.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
        ((s.regs 4).toNat - 8, (s.regs 4).toNat)] →
      S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat →
      (∀ c, c < 256 → S.mem.readLE (5175774 + c) 1 = (hexNib c).getD 255) →
      s.mem.accessible ((s.regs 4).toNat - 8) 32 true = true → s.mem.accessible z.toNat 32 true = true →
      s.mem.accessible hp.toNat len.toNat false = true → s.mem.accessible 5175774 256 false = true →
      s.mem.accessible 5987120 96 false = true →
      s.mem.accessible (s.regs 4).toNat 8 false = true →
      ReachesRet (Extracted.program) (retAddrOf s) S (LoopQ s z hp len) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i e0 e1 ri hn hi he0 he1 he10 he0l he1g he01 hr1 hr2 hpc h0 h3 h2 h6 h1 h8 h7 h4 h5 h14 hx15 hdf hfs hv1 hv2 hlimbs hfr hbp htab hSw hSz hSs hSt hSe hSr
    have hb : s.mem.readLE (hp.toNat + ri) 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem (hp.toNat + ri) 1
    have hc : s.mem.readLE (hp.toNat + ri) 1 % 4294967296 = s.mem.readLE (hp.toNat + ri) 1 := Nat.mod_eq_of_lt (by omega)
    have hn256 := hexNib_getD_lt (s.mem.readLE (hp.toNat + ri) 1)
    janus64_run until [innerHead]
    · -- exit: all limbs done
      have hi3 : i = 3 := by omega
      subst hi3
      have hri : ri = e0 := by omega
      subst hri
      have he1' : e1 = 2 := by have := he1; unfold hexEnd at this; omega
      subst he1'
      unfold LoopQ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfr, ?_⟩
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · simp [setRegF_apply, h14]
      · simp [hx15]
      · rfl
      · simp [hfs]
      · refine Or.inl ⟨?_, ?_, allHex_join hv2 hv1, ?_⟩
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · intro j hj
          rw [hlimbs j hj]
          by_cases hj3 : j < 3
          · simp [hj3]
          · have : j = 3 := by omega
            subst this
            simp [hexLimb, he0, he1]
    · -- next limb, 16 or more digits left
      rename_i hA hB
      have hi3 : i + 1 ≤ 3 := by omega
      have hri : ri = e0 := by omega
      subst hri
      have hC' : 18 ≤ e1 := by rw [toInt_sub16 e1 (by omega)] at hbr; omega
      have he1' : e1 - 16 = hexEnd len.toNat (i + 1 + 1) := by
        have := he1; unfold hexEnd at this ⊢; omega
      refine ih (17 * (3 - (i + 1)) + (e1 - (e1 - 16))) (by omega) _ (i + 1) e1 (e1 - 16) (e1 - 16) rfl hi3 he1 he1' (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (allHex_join hv2 hv1) (allHex_nil _ _) ?_ hfr hbp htab hSw hSz hSs hSt hSe hSr
      · simp [setRegF_apply, h0]
      · simp [setRegF_apply, h3]
      · simp [setRegF_apply, h2]
      · simp [setRegF_apply, ofNat_add1]
      · simp [setRegF_apply]
      · simp [setRegF_apply, ofNat_sub16 e1 (by omega) (by omega)]
      · simp [setRegF_apply, ofNat_sub16 e1 (by omega) (by omega)]
      · simp [setRegF_apply, h4]
      · simp [setRegF_apply, h5]
      · simp [setRegF_apply, h14]
      · simp [hx15]
      · rfl
      · simp [hfs]
      · intro j hj
        rw [hlimbs j hj]
        rcases Nat.lt_trichotomy j i with h | h | h
        · simp [h, show j < i + 1 by omega]
        · subst h
          simp [hexLimb, he0, he1]
        · have h1 : ¬ j < i := by omega
          have h2 : j ≠ i := by omega
          have h3 : ¬ j < i + 1 := by omega
          by_cases h4 : j = i + 1
          · subst h4; simp [hexSum, h1]
          · simp [h1, h2, h3, h4]
    · -- next limb, fewer than 16 digits left
      rename_i hA hB
      have hi3 : i + 1 ≤ 3 := by omega
      have hri : ri = e0 := by omega
      subst hri
      have hC' : e1 ≤ 17 := by rw [toInt_sub16 e1 (by omega)] at hbr; omega
      have he1' : 2 = hexEnd len.toNat (i + 1 + 1) := by
        have := he1; unfold hexEnd at this ⊢; omega
      refine ih (17 * (3 - (i + 1)) + (e1 - 2)) (by omega) _ (i + 1) e1 2 2 rfl hi3 he1 he1' (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (allHex_join hv2 hv1) (allHex_nil _ _) ?_ hfr hbp htab hSw hSz hSs hSt hSe hSr
      · simp [setRegF_apply, h0]
      · simp [setRegF_apply, h3]
      · simp [setRegF_apply, h2]
      · simp [setRegF_apply, ofNat_add1]
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · simp [setRegF_apply, h4]
      · simp [setRegF_apply, h5]
      · simp [setRegF_apply, h14]
      · simp [hx15]
      · rfl
      · simp [hfs]
      · intro j hj
        rw [hlimbs j hj]
        rcases Nat.lt_trichotomy j i with h | h | h
        · simp [h, show j < i + 1 by omega]
        · subst h
          simp [hexLimb, he0, he1]
        · have h1 : ¬ j < i := by omega
          have h2 : j ≠ i := by omega
          have h3 : ¬ j < i + 1 := by omega
          by_cases h4 : j = i + 1
          · subst h4; simp [hexSum, h1]
          · simp [h1, h2, h3, h4]
    · -- bad digit
      rename_i hA hB
      have hC' : (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 = 255 := by
        rw [hc] at hB
        exact (cmp255 _ hn256).1 hB
      have hn := hexNib_none_of hC'
      unfold LoopQ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfr, ?_⟩
      · simp [setRegF_apply]
      · simp [setRegF_apply]
      · simp [setRegF_apply, h14]
      · simp [hx15]
      · rfl
      · simp [hfs]
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · simp [setRegF_apply]
        · simp [setRegF_apply]
        · intro hall
          have := hall ri (by omega) (by omega)
          have h2 : bytesAt s.mem hp.toNat ri = s.mem.readLE (hp.toNat + ri) 1 := rfl
          rw [h2, hn] at this
          simp at this
    · -- next digit
      rename_i hA hB
      have hC' : (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 ≠ 255 := by
        intro h; apply hbr
        rw [hc]; exact (cmp255 _ hn256).2 h
      obtain ⟨hsome, hval⟩ := hexNib_some_of hC'
      have hv : S.mem.readLE (z.toNat + i * 8) 8 = hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1) := by
        have := hlimbs i (by omega)
        rw [Nat.mul_comm 8 i] at this
        simpa using this
      have hlt : hexSum (bytesAt s.mem hp.toNat) e1 (ri + 1 - e1) < 2 ^ 64 := by
        have h1 := hexSum_lt (bytesAt s.mem hp.toNat) e1 (ri + 1 - e1)
        have h2 : 16 ^ (ri + 1 - e1) ≤ 16 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
        have h3 : (16 : Nat) ^ 16 = 2 ^ 64 := by decide
        omega
      have hsum : hexSum (bytesAt s.mem hp.toNat) e1 (ri + 1 - e1) =
          (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 + hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1) * 16 := by
        rw [show ri + 1 - e1 = (ri - e1) + 1 by omega, hexSum]
        have : e1 + (ri - e1) = ri := by omega
        rw [this]
        have : hexDigit (bytesAt s.mem hp.toNat) ri = (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 := by
          show (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 0 = _
          rw [← hval]
        omega
      have hv15 : hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1) * 16 < 2 ^ 64 := by
        have h1 := hexSum_lt (bytesAt s.mem hp.toNat) e1 (ri - e1)
        have h2 : 16 ^ (ri - e1) ≤ 16 ^ 15 := Nat.pow_le_pow_right (by omega) (by omega)
        have h3 : (16 : Nat) ^ 15 = 2 ^ 60 := by decide
        omega
      refine ih (17 * (3 - i) + (e0 - (ri + 1))) (by omega) _ i e0 e1 (ri + 1) rfl hi he0 he1 he10 he0l he1g he01 (by omega) (by omega) rfl ?h0 ?h3 ?h2 ?h6 ?h1 ?h8 ?h7 ?h4 ?h5 ?h14 ?hx15 ?hdf ?hfs hv1 (allHex_step hv2 hsome) ?hlimbs ?hfr ?hbp ?htab hSw hSz hSs hSt hSe hSr
      case h0 => simp [setRegF_apply, h0]
      case h3 => simp [setRegF_apply, h3]
      case h2 => simp [setRegF_apply, h2]
      case h6 => simp [setRegF_apply, h6]
      case h1 => simp [setRegF_apply, h1]
      case h8 => simp [setRegF_apply, h8]
      case h7 => simp [setRegF_apply]
      case h4 => simp [setRegF_apply, h4]
      case h5 => simp [setRegF_apply, h5]
      case h14 => simp [setRegF_apply, h14]
      case hx15 => simp [hx15]
      case hdf => rfl
      case hfs => simp [hfs]
      case hlimbs =>
        intro j hj
        dsimp only
        rcases Nat.lt_trichotomy j i with h | h | h
        · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hlimbs j hj]
          simp [h]
        · subst h
          rw [Nat.mul_comm 8 j, Janus.Arm64.Memory.readLE_writeLE_self, hv]
          have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
          have e1' : (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 % 256 % 4294967296 =
              (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 := by omega
          have e2' : hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1) * 16 % 18446744073709551616 =
              hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1) * 16 := Nat.mod_eq_of_lt hv15
          rw [hc, e1', e2', e, if_neg (Nat.lt_irrefl _), if_pos rfl, ← hsum]
          exact Nat.mod_eq_of_lt hlt
        · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), hlimbs j hj]
          have h1 : ¬ j < i := by omega
          have h2 : j ≠ i := by omega
          simp [h1, h2]
      case hfr =>
        exact (hfr.writeLE _ (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE
          _ (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
      case hbp =>
        dsimp only
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hbp
      case htab =>
        intro c hc'
        dsimp only
        rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega),
          Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact htab c hc'


/-- the address of the package variable (an `error` interface value) for each parse error tag -/
def errAddrOf (e : Nat) : Nat :=
  if e = 0 then 5987120 else if e = 1 then 5987152 else if e = 2 then 5987168
  else if e = 3 then 5987184 else if e = 4 then 5987200 else 5987136

theorem errAddrOf_bounds (e : Nat) : 5987120 ≤ errAddrOf e ∧ errAddrOf e + 16 ≤ 5987216 := by
  unfold errAddrOf
  by_cases h0 : e = 0
  · simp [h0]
  by_cases h1 : e = 1
  · simp [h1]
  by_cases h2 : e = 2
  · simp [h2]
  by_cases h3 : e = 3
  · simp [h3]
  by_cases h4 : e = 4
  · simp [h4]
  simp [h0, h1, h2, h3, h4]

def FromHexPre (z hp len : BitVec 64) (s : State) : Prop :=
  RetOK s ∧ s.regs 0 = z ∧ s.regs 3 = hp ∧ s.regs 1 = len ∧ Buffer s z 32 true ∧ Buffer s hp len.toNat false ∧
  (∀ c, c < 256 → s.mem.readLE (5175774 + c) 1 = (hexNib c).getD 255) ∧ s.mem.accessible 5175774 256 false = true ∧
  (z.toNat + 32 ≤ 5175774 ∨ 5175774 + 256 ≤ z.toNat) ∧
  ((s.regs 4).toNat - 8 + 32 ≤ 5175774 ∨ 5175774 + 256 ≤ (s.regs 4).toNat - 8) ∧
  s.mem.accessible 5987120 96 false = true ∧ StackWritable s 8 24 ∧
  (z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat) ∧
  (z.toNat + 32 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ z.toNat) ∧
  (hp.toNat + len.toNat ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ hp.toNat) ∧
  (z.toNat + 32 ≤ 5987120 ∨ 5987216 ≤ z.toNat) ∧
  (5987216 ≤ (s.regs 4).toNat - 8 ∨ (s.regs 4).toNat + 24 ≤ 5987120) ∧
  (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

def FromHexPost (z hp len : BitVec 64) (s s' : State) : Prop :=
  s'.rip = retAddrOf s ∧ s'.regs 4 = s.regs 4 + 8 ∧ s'.regs 5 = s.regs 5 ∧ s'.regs 14 = s.regs 14 ∧
  s'.xmm 15 = s.xmm 15 ∧ s'.df = s.df ∧ s'.fsBase = s.fsBase ∧
  Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
    ((s.regs 4).toNat - 8, (s.regs 4).toNat)] ∧
  (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 3 = 0 ∧ Janus.Spec.val256 s'.mem z.toNat = v) ∧
  (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
      s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))

theorem rr_mono {p : Janus.Amd64.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

theorem post_err (s s' : State) (z hp len : BitVec 64) (E : Nat)
    (hpar : parseHex (bytesAt s.mem hp.toNat) len.toNat = .error E)
    (hrip : s'.rip = retAddrOf s) (h4 : s'.regs 4 = s.regs 4 + 8) (h5 : s'.regs 5 = s.regs 5)
    (h14 : s'.regs 14 = s.regs 14) (hx : s'.xmm 15 = s.xmm 15) (hdf : s'.df = s.df) (hfs : s'.fsBase = s.fsBase)
    (hfr : Janus.MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24),
      ((s.regs 4).toNat - 8, (s.regs 4).toNat)])
    (r0 : s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf E) 8))
    (r3 : s'.regs 3 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf E + 8) 8)) : FromHexPost z hp len s s' := by
  refine ⟨hrip, h4, h5, h14, hx, hdf, hfs, hfr, ?_, ?_⟩
  · intro v hv; rw [hpar] at hv; cases hv
  · intro e he; rw [hpar] at he; cases he; exact ⟨r0, r3⟩

theorem post_of_loopQ (s s' : State) (z hp len : BitVec 64) (hn3 : 3 ≤ len.toNat) (hn66 : len.toNat ≤ 66)
    (h0 : bytesAt s.mem hp.toNat 0 = 48) (h1 : bytesAt s.mem hp.toNat 1 = 120 ∨ bytesAt s.mem hp.toNat 1 = 88)
    (h2 : 3 < len.toNat → bytesAt s.mem hp.toNat 2 ≠ 48) (hq : LoopQ s z hp len s') :
    FromHexPost z hp len s s' := by
  obtain ⟨hrip, h4, h5, h14, hx, hdf, hfs, hfr, hres⟩ := hq
  refine ⟨hrip, h4, h5, h14, hx, hdf, hfs, hfr, ?_, ?_⟩
  · intro v hv
    rw [pe_body _ _ hn3 hn66 h0 h1 h2] at hv
    rcases hres with ⟨r0, r1, hall, hl⟩ | ⟨r0, r1, hnall⟩
    · rw [if_pos hall] at hv
      cases hv
      refine ⟨r0, r1, ?_⟩
      have l0 := hl 0 (by omega)
      have l1 := hl 1 (by omega)
      have l2 := hl 2 (by omega)
      have l3 := hl 3 (by omega)
      have ht := hexSum_tail (bytesAt s.mem hp.toNat) len.toNat (by omega) 4
      have he4 : hexEnd len.toNat 4 = 2 := by unfold hexEnd; omega
      rw [he4] at ht
      rw [show z.toNat + 8 * 0 = z.toNat from rfl] at l0
      rw [show z.toNat + 8 * 1 = z.toNat + 8 from rfl] at l1
      rw [show z.toNat + 8 * 2 = z.toNat + 16 from rfl] at l2
      rw [show z.toNat + 8 * 3 = z.toNat + 24 from rfl] at l3
      rw [Janus.Spec.val256_limbs, l0, l1, l2, l3, ht]
      simp only [hexW, Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.reducePow, Nat.reduceMul]
      omega
    · rw [if_neg hnall] at hv; cases hv
  · intro e he
    rw [pe_body _ _ hn3 hn66 h0 h1 h2] at he
    rcases hres with ⟨r0, r1, hall, hl⟩ | ⟨r0, r1, hnall⟩
    · rw [if_pos hall] at he; cases he
    · rw [if_neg hnall] at he; cases he; exact ⟨r0, r1⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 10000 in
theorem fromHex_sum (impl : List Janus.Segment) (z hp len : BitVec 64) :
    Summary Extracted.program fh (FromHexPre z hp len) (FromHexPost z hp len) := by
  intro s hpc ⟨⟨hr1, hr2, hx15, hdf⟩, hz0, hp0, hl0, ⟨hzw, hz⟩, ⟨hpw, hp⟩, htab0, hSt0, hzt, hst, herr, ⟨hlow, hnw, hacc⟩,
    hdzh, hdzs, hdhs, hdzg, hdgs, hnn⟩
  subst hz0 hp0 hl0
  simp only [regSP] at hacc hlow hnw
  have hn1 : s.mem.readLE 5987120 8 ≠ 0 := hnn 0 (by decide)
  have hn2 : s.mem.readLE 5987136 8 ≠ 0 := hnn 5 (by decide)
  have hn3 : s.mem.readLE 5987152 8 ≠ 0 := hnn 1 (by decide)
  have hn4 : s.mem.readLE 5987168 8 ≠ 0 := hnn 2 (by decide)
  have hn5 : s.mem.readLE 5987184 8 ≠ 0 := hnn 3 (by decide)
  have hn6 : s.mem.readLE 5987200 8 ≠ 0 := hnn 4 (by decide)
  have e0 : bytesAt s.mem (s.regs 3).toNat 0 = s.mem.readLE (s.regs 3).toNat 1 := rfl
  have e1 : bytesAt s.mem (s.regs 3).toNat 1 = s.mem.readLE ((s.regs 3).toNat + 1) 1 := rfl
  have e2 : bytesAt s.mem (s.regs 3).toNat 2 = s.mem.readLE ((s.regs 3).toNat + 2) 1 := rfl
  have hb1 : s.mem.readLE ((s.regs 3).toNat + 1) 1 < 256 := by simpa using Janus.Arm64.Memory.readLE_lt s.mem ((s.regs 3).toNat + 1) 1
  janus64_run until [innerHead]
  all_goals (try simp only [cmp120 _ hb1, cmp88 _ hb1] at *)
  all_goals first
    | (have hpar : parseHex (bytesAt s.mem (s.regs 3).toNat) (s.regs 1).toNat = Except.error 0 := by
         have h : (s.regs 1).toNat = 0 := by omega
         rw [h]; exact pe_empty _
       exact post_err _ _ _ _ _ _ hpar (by simp [retAddrOf]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
         (by simp [setRegF_apply]) (by simp) (by simp [hdf]) (by simp) (by janus_frame)
         (by simp [errAddrOf, setRegF_apply]) (by simp [errAddrOf, setRegF_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 3).toNat) (s.regs 1).toNat = Except.error 1 := pe_missing _ _ (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar (by simp [retAddrOf]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
         (by simp [setRegF_apply]) (by simp) (by simp [hdf]) (by simp) (by janus_frame)
         (by simp [errAddrOf, setRegF_apply]) (by simp [errAddrOf, setRegF_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 3).toNat) (s.regs 1).toNat = Except.error 2 := pe_emptyNum _ _ (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar (by simp [retAddrOf]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
         (by simp [setRegF_apply]) (by simp) (by simp [hdf]) (by simp) (by janus_frame)
         (by simp [errAddrOf, setRegF_apply]) (by simp [errAddrOf, setRegF_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 3).toNat) (s.regs 1).toNat = Except.error 3 := pe_lead _ _ (by omega) (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar (by simp [retAddrOf]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
         (by simp [setRegF_apply]) (by simp) (by simp [hdf]) (by simp) (by janus_frame)
         (by simp [errAddrOf, setRegF_apply]) (by simp [errAddrOf, setRegF_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 3).toNat) (s.regs 1).toNat = Except.error 4 := pe_big _ _ (by omega) (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar (by simp [retAddrOf]) (by simp [setRegF_apply]) (by simp [setRegF_apply])
         (by simp [setRegF_apply]) (by simp) (by simp [hdf]) (by simp) (by janus_frame)
         (by simp [errAddrOf, setRegF_apply]) (by simp [errAddrOf, setRegF_apply]))
    | skip
  all_goals
    refine rr_mono (loop impl s (s.regs 0) (s.regs 3) (s.regs 1) (by omega) (by omega) hzw hpw hp hdzh hdhs hdzs hzt hdzg
       (by omega) hlow hnw hr2 (17 * (3 - 0) + ((s.regs 1).toNat - hexEnd (s.regs 1).toNat 1)) _ 0 (s.regs 1).toNat
       (hexEnd (s.regs 1).toNat 1) (hexEnd (s.regs 1).toNat 1) rfl (by omega) (by unfold hexEnd; omega) rfl
       (by unfold hexEnd; omega) (by omega) (by unfold hexEnd; omega) (by unfold hexEnd; omega) (Nat.le_refl _)
       (by unfold hexEnd; omega) rfl ?h0 ?h3 ?h2 ?h6 ?h1 ?h8 ?h7 ?h4 ?h5 ?h14 ?hx15 ?hdf ?hfs (allHex_nil _ _) (allHex_nil _ _)
       ?hlimbs ?hfr ?hbp ?htab hacc hz hp hSt0 herr hr1)
       (fun s' hq => post_of_loopQ s s' _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) hq)
    case h0 => simp [setRegF_apply]
    case h3 => simp [setRegF_apply]
    case h2 => simp [setRegF_apply]
    case h6 => simp [setRegF_apply]
    case h1 => simp [setRegF_apply]
    case h4 => simp [setRegF_apply]
    case h5 => simp [setRegF_apply]
    case h14 => simp [setRegF_apply]
    case hx15 => simp [hx15]
    case hdf => simp [hdf]
    case hfs => simp
    case h8 =>
      simp [setRegF_apply]
      have ht := toInt_sub16' (s.regs 1) (by omega)
      first
      | (rw [ofNat_sub16' (s.regs 1) (by omega)]; congr 1; unfold hexEnd; omega)
      | (have h : hexEnd (s.regs 1).toNat 1 = 2 := by unfold hexEnd; omega
         rw [h])
    case h7 =>
      simp [setRegF_apply]
      have ht := toInt_sub16' (s.regs 1) (by omega)
      first
      | (rw [ofNat_sub16' (s.regs 1) (by omega)]; congr 1; unfold hexEnd; omega)
      | (have h : hexEnd (s.regs 1).toNat 1 = 2 := by unfold hexEnd; omega
         rw [h])
    case hlimbs =>
      intro j hj
      dsimp only
      rw [zero_read16 _ _ j hj]
      simp [hexSum]
    case hfr =>
      exact (((Janus.MemFrame.refl s.mem _).writeLE _ (r := ((s.regs 4).toNat - 8, (s.regs 4).toNat)) (by simp)
        (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 4).toNat + 16, (s.regs 4).toNat + 24))
        (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE _ (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32))
        (by simp) (by dsimp only; omega) (by dsimp only; omega) |>.writeLE _ (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32))
        (by simp) (by dsimp only; omega) (by dsimp only; omega)
    case hbp =>
      dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h8]; exact Nat.mod_eq_of_lt (s.regs 5).isLt
    case htab =>
      intro c hc
      dsimp only
      simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
      exact htab0 c hc
  all_goals (trace_state; fail "x")

end Fv256.Amd64.SetFromHexLoops
