import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.C

namespace Fv256.Arm64.SetFromHexLoops

abbrev fh : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).fromHex"
abbrev outerHead : Nat := fh + 0x10c

/-- address of the sentinel error variable loaded by the ADRP/ADD pair at word index `i` of `fromHex` -/
def errAddr (i : Nat) : Nat :=
  adrpLdTarget (fh + 4 * i) (segWord Extracted.program "github.com/holiman/uint256.(*Int).fromHex" i)
    (segWord Extracted.program "github.com/holiman/uint256.(*Int).fromHex" (i + 1)) 0

/-- the six sentinel error variables (`ErrEmptyString`, `ErrSyntax`, `ErrMissingPrefix`, `ErrEmptyNumber`, `ErrLeadingZero`, `ErrBig256Range`)
are consecutive 16-byte interface values at these addresses (`.data`, not copied by the extraction: the precondition provides them). -/
def eEmpty : Nat := 1792752
def eSyn : Nat := 1792768
def ePrefix : Nat := 1792784
def eNum : Nat := 1792800
def eLead : Nat := 1792816
def eBig : Nat := 1792832

theorem err_addrs : errAddr 8 = eEmpty ∧ errAddr 22 = ePrefix ∧ errAddr 30 = eNum ∧ errAddr 39 = eLead ∧ errAddr 54 = eBig ∧
    errAddr 98 = eSyn := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide


abbrev innerHead : Nat := fh + 0x144
abbrev tbl : Nat := 1001813

/-- the byte sequence of the string -/
def bytesAt (m : Memory) (hp : Nat) : Nat → Nat := fun k => m.readLE (hp + k) 1

theorem allHex_join {b : Nat → Nat} {a c d : Nat} (h1 : allHex b a c) (h2 : allHex b c d) : allHex b a d := by
  intro k hk1 hk2
  by_cases h : k < c
  · exact h1 k hk1 h
  · exact h2 k (by omega) hk2

theorem allHex_step {b : Nat → Nat} {a r : Nat} (h : allHex b a r) (hr : (hexNib (b r)).isSome) :
    allHex b a (r + 1) := by
  intro k hk1 hk2
  by_cases h' : k < r
  · exact h k hk1 h'
  · have : k = r := by omega
    subst this; exact hr

theorem allHex_nil (b : Nat → Nat) (a : Nat) : allHex b a a := fun k h1 h2 => by omega

theorem hexNib_lt16 {c v : Nat} (h : hexNib c = some v) : v < 16 := by
  unfold hexNib at h
  by_cases h1 : 48 ≤ c ∧ c ≤ 57
  · simp [h1] at h; omega
  · by_cases h2 : 97 ≤ c ∧ c ≤ 102
    · simp [h1, h2] at h; omega
    · by_cases h3 : 65 ≤ c ∧ c ≤ 70
      · simp [h1, h2, h3] at h; omega
      · simp [h1, h2, h3] at h

theorem hexNib_none_of {c : Nat} (h : (hexNib c).getD 255 = 255) : hexNib c = none := by
  cases h' : hexNib c with
  | none => rfl
  | some v => rw [h'] at h; simp at h; have := hexNib_lt16 h'; omega

theorem hexNib_some_of {c : Nat} (h : (hexNib c).getD 255 ≠ 255) :
    (hexNib c).isSome = true ∧ (hexNib c).getD 255 = (hexNib c).getD 0 := by
  cases h' : hexNib c with
  | none => rw [h'] at h; simp at h
  | some v => simp


theorem hexNib_getD_lt (c : Nat) : (hexNib c).getD 255 < 256 := by
  cases h : hexNib c with
  | none => simp
  | some v => have := hexNib_lt16 h; simp; omega

theorem toInt_sub16 (e : Nat) (h : e < 2^32) : (BitVec.ofNat 64 e - 16#64).toInt = (e : Int) - 16 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_sub16 (e : Nat) (h : 16 ≤ e) (h2 : e < 2^32) : BitVec.ofNat 64 e - 16#64 = BitVec.ofNat 64 (e - 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ofNat_add1 (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sp_add16 (a t : BitVec 64) (h : a.toNat + 16 = t.toNat) : a + 16#64 = t := by
  apply BitVec.eq_of_toNat_eq
  have := t.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sp_sub24 (t : BitVec 64) (h : 24 ≤ t.toNat) : (t - 24#64).toNat = t.toNat - 24 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := t.isLt
  omega

theorem sw32 (N : Nat) (h : N < 256) : (BitVec.setWidth 32 (BitVec.ofNat 64 N)).toNat = N := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- postcondition of the digit loop (relative to the entry state `s` of `fromHex`) -/
def LoopQ (s : State) (z hp len : BitVec 64) (s' : State) : Prop :=
  s'.pc = s.regs regLR ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
  s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
  ((s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ allHex (bytesAt s.mem hp.toNat) 2 len.toNat ∧
      ∀ j, j < 4 → s'.mem.readLE (z.toNat + 8 * j) 8 = hexLimb (bytesAt s.mem hp.toNat) len.toNat j) ∨
   (s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE 1792768 8) ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE 1792776 8) ∧
      ¬ allHex (bytesAt s.mem hp.toNat) 2 len.toNat))

/- the loop invariant at the inner-loop head (`CMP end, ri`): limb `i` is being accumulated, `ri` digits (from `e (i+1)`) done -/
set_option maxHeartbeats 16000000 in
theorem loop (impl : List Segment) (s : State) (z hp len : BitVec 64) (hL : 3 ≤ len.toNat) (hL2 : len.toNat ≤ 66)
    (h30a : (s.regs 30).toNat % 4 = 0) (h30b : (s.regs 30).toNat < 2 ^ 56)
    (hz' : z.toNat + 32 ≤ 2 ^ 48) (hs' : hp.toNat + len.toNat ≤ 2 ^ 48)
    (hsa : s.mem.accessible hp.toNat len.toNat false = true)
    (hdz : z.toNat + 32 ≤ hp.toNat ∨ hp.toNat + len.toNat ≤ z.toNat)
    (hdst : hp.toNat + len.toNat ≤ s.sp.toNat - 24 ∨ s.sp.toNat + 24 ≤ hp.toNat)
    (hdzs : z.toNat + 32 ≤ s.sp.toNat - 24 ∨ s.sp.toNat + 24 ≤ z.toNat)
    (hzt : z.toNat + 32 ≤ 1001813 ∨ 1001813 + 256 ≤ z.toNat)
    (hgz : z.toNat + 32 ≤ 1792752 ∨ 1792848 ≤ z.toNat)
    (hgs : s.sp.toNat + 24 ≤ 1792752 ∨ 1792848 ≤ s.sp.toNat - 24)
    (hsp : 24 ≤ s.sp.toNat) (hspa : s.sp.toNat + 24 ≤ 2 ^ 48) (hal : s.sp.toNat % 16 = 0) :
    ∀ n (S : State) (i e0 e1 ri : Nat), n = 17 * (3 - i) + (e0 - ri) → i ≤ 3 →
      e0 = hexEnd len.toNat i → e1 = hexEnd len.toNat (i + 1) → e1 ≤ e0 → e0 ≤ len.toNat → 2 ≤ e1 → e0 ≤ e1 + 16 →
      e1 ≤ ri → ri ≤ e0 →
      S.pc = BitVec.ofNat 64 innerHead → S.regs 0 = z → S.regs 1 = hp → S.regs 3 = len →
      S.regs 4 = BitVec.ofNat 64 i → S.regs 2 = BitVec.ofNat 64 e0 →
      S.regs 6 = BitVec.ofNat 64 e1 → S.regs 5 = BitVec.ofNat 64 ri →
      S.sp.toNat + 16 = s.sp.toNat → S.regs 28 = s.regs 28 → S.regs 18 = s.regs 18 → S.regs 29 = s.sp - 24#64 →
      S.regs 30 = s.regs 30 →
      allHex (bytesAt s.mem hp.toNat) e0 len.toNat →
      allHex (bytesAt s.mem hp.toNat) e1 ri →
      (∀ j, j < 4 → S.mem.readLE (z.toNat + 8 * j) 8 =
        if j < i then hexLimb (bytesAt s.mem hp.toNat) len.toNat j
        else if j = i then hexSum (bytesAt s.mem hp.toNat) e1 (ri - e1)
        else 0) →
      MemFrame s.mem S.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] →
      S.mem.readLE S.sp.toNat 8 = (s.regs 30).toNat → S.mem.readLE (S.sp.toNat - 8) 8 = (s.regs 29).toNat →
      (∀ c, c < 256 → S.mem.readLE (1001813 + c) 1 = (hexNib c).getD 255) →
      s.mem.accessible (s.sp.toNat - 24) 48 true = true → s.mem.accessible z.toNat 32 true = true →
      s.mem.accessible hp.toNat len.toNat false = true → s.mem.accessible 1001813 256 false = true →
      s.mem.accessible 1792752 96 false = true →
      ReachesRet (Extracted.program.link impl) (s.regs regLR) S (LoopQ s z hp len) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro S i e0 e1 ri hn hi he0 he1 he10 he0l he1g he01 hr1 hr2 hpc h0 h1 h3 h4 h2 h6 h5 hsp' h28 h18 h29 h30 hv1 hv2 hlimbs hfr hlr hfp htab hSw hSz hSs hSt hSe
    have hSal : S.sp.toNat % 16 = 0 := by omega
    have hb : s.mem.readLE (hp.toNat + ri) 1 < 256 := by simpa using Memory.readLE_lt s.mem (hp.toNat + ri) 1
    janus_run until [innerHead, fh + 0x184, fh + 0x19c]
    · -- exit: all limbs done
      simp only [hlr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      janus_run
      have hi3 : i = 3 := by omega
      subst hi3
      have hri : ri = e0 := by omega
      subst hri
      have he1' : e1 = 2 := by have := he1; unfold hexEnd at this; omega
      subst he1'
      unfold LoopQ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hfr, ?_⟩
      · exact sp_add16 _ _ hsp'
      · simp [setReg_apply, h28]
      · simp [setReg_apply, hfp]
      · simp [setReg_apply]
      · simp [setReg_apply, h18]
      · refine Or.inl ⟨?_, ?_, allHex_join hv2 hv1, ?_⟩
        · simp [setReg_apply]
        · simp [setReg_apply]
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
      refine ih (17 * (3 - (i + 1)) + (e1 - (e1 - 16))) (by omega) _ (i + 1) e1 (e1 - 16) (e1 - 16) rfl hi3 he1 he1' (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsp' ?_ ?_ ?_ ?_ (allHex_join hv2 hv1) (allHex_nil _ _) ?_ hfr hlr hfp htab hSw hSz hSs hSt hSe
      · simp [setReg_apply, h0]
      · simp [setReg_apply, h1]
      · simp [setReg_apply, h3]
      · simp [setReg_apply, ofNat_add1]
      · simp [setReg_apply]
      · simp [setReg_apply, ofNat_sub16 e1 (by omega) (by omega)]
      · simp [setReg_apply, ofNat_sub16 e1 (by omega) (by omega)]
      · simp [setReg_apply, h28]
      · simp [setReg_apply, h18]
      · simp [setReg_apply, h29]
      · simp [setReg_apply, h30]
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
      refine ih (17 * (3 - (i + 1)) + (e1 - 2)) (by omega) _ (i + 1) e1 2 2 rfl hi3 he1 he1' (by omega) (by omega) (by omega) (by omega) (Nat.le_refl _) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsp' ?_ ?_ ?_ ?_ (allHex_join hv2 hv1) (allHex_nil _ _) ?_ hfr hlr hfp htab hSw hSz hSs hSt hSe
      · simp [setReg_apply, h0]
      · simp [setReg_apply, h1]
      · simp [setReg_apply, h3]
      · simp [setReg_apply, ofNat_add1]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp [setReg_apply]
      · simp [setReg_apply, h28]
      · simp [setReg_apply, h18]
      · simp [setReg_apply, h29]
      · simp [setReg_apply, h30]
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
      have hbr' := hbr
      simp only [hlr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      janus_run
      have hC' : (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 = 255 := by
        rw [sw32 _ (hexNib_getD_lt _)] at hbr'
        exact hbr'
      have hn := hexNib_none_of hC'
      unfold LoopQ
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hfr, ?_⟩
      · exact sp_add16 _ _ hsp'
      · simp [setReg_apply, h28]
      · simp [setReg_apply, hfp]
      · simp [setReg_apply]
      · simp [setReg_apply, h18]
      · refine Or.inr ⟨?_, ?_, ?_⟩
        · simp [setReg_apply]
        · simp [setReg_apply]
        · intro hall
          have := hall ri (by omega) (by omega)
          have h2 : bytesAt s.mem hp.toNat ri = s.mem.readLE (hp.toNat + ri) 1 := rfl
          rw [h2, hn] at this
          simp at this
    · -- next digit
      rename_i hA hB
      have hC' : (hexNib (s.mem.readLE (hp.toNat + ri) 1)).getD 255 ≠ 255 := by
        intro h; apply hbr
        rw [sw32 _ (hexNib_getD_lt _)]; exact h
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
      refine ih (17 * (3 - i) + (e0 - (ri + 1))) (by omega) _ i e0 e1 (ri + 1) rfl hi he0 he1 he10 he0l he1g he01 (by omega) (by omega) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsp' ?_ ?_ ?_ ?_ hv1 (allHex_step hv2 hsome) ?_ ?_ ?_ ?_ ?_ hSw hSz hSs hSt hSe
      · simp [setReg_apply, h0]
      · simp [setReg_apply, h1]
      · simp [setReg_apply, h3]
      · simp [setReg_apply, h4]
      · simp [setReg_apply, h2]
      · simp [setReg_apply, h6]
      · simp [setReg_apply, ofNat_add1]
      · simp [setReg_apply, h28]
      · simp [setReg_apply, h18]
      · simp [setReg_apply, h29]
      · simp [setReg_apply, h30]
      · intro j hj
        dsimp only
        rcases Nat.lt_trichotomy j i with h | h | h
        · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            hlimbs j hj]
          simp [h]
        · subst h
          rw [Nat.mul_comm 8 j, Memory.readLE_writeLE_self, hv]
          have e : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
          rw [e, if_neg (Nat.lt_irrefl _), if_pos rfl, ← hsum]
          exact Nat.mod_eq_of_lt hlt
        · rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
            hlimbs j hj]
          have h1 : ¬ j < i := by omega
          have h2 : j ≠ i := by omega
          simp [h1, h2]
      · exact (hfr.writeLE _ (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)).writeLE
          _ (r := (z.toNat, z.toNat + 32)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
      · dsimp only
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hlr
      · dsimp only
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact hfp
      · intro c hc
        dsimp only
        rw [Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
        exact htab c hc


theorem toInt_sub16' (x : BitVec 64) (h : x.toNat < 2 ^ 32) : (x - 16#64).toInt = (x.toNat : Int) - 16 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  split <;> omega

theorem ofNat_sub16' (x : BitVec 64) (h : 16 ≤ x.toNat) : x - 16#64 = BitVec.ofNat 64 (x.toNat - 16) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sp_sub16 (t : BitVec 64) (h : 16 ≤ t.toNat) : (t - 16#64).toNat = t.toNat - 16 := by
  have := t.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem zero_read (m : Memory) (z j : Nat) (hj : j < 4) :
    ((((m.writeLE (z + 16) 8 0).writeLE (z + 24) 8 0).writeLE z 8 0).writeLE (z + 8) 8 0).readLE (z + 8 * j) 8 = 0 := by
  have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [show z + 8 * 0 = z by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]
  · rw [show z + 8 * 1 = z + 8 by omega, Memory.readLE_writeLE_self]
  · rw [show z + 8 * 2 = z + 16 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_self]
  · rw [show z + 8 * 3 = z + 24 by omega, Memory.readLE_writeLE_of_disjoint _ _ (by omega),
      Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_self]

set_option maxRecDepth 100000 in
theorem tabData : ∀ c, c < 256 → (dataRead Extracted.program (1001813 + c) 1).isSome = true ∧
    dataReadD Extracted.program (1001813 + c) 1 = (hexNib c).getD 255 := by
  decide

theorem tab_vals {m : Memory} (h : Extracted.program.DataLoaded m) :
    ∀ c, c < 256 → m.readLE (1001813 + c) 1 = (hexNib c).getD 255 := by
  intro c hc
  obtain ⟨h1, h2⟩ := tabData c hc
  rw [readLE_dataReadD h _ _ h1, h2]

set_option maxRecDepth 100000 in
theorem tab_isSome : (dataRead Extracted.program 1001813 256).isSome = true := by decide

theorem disj_data {p : Program} {m : Memory} (h : p.DataLoaded m) {t k : Nat}
    (hv : (dataRead p t k).isSome = true) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ t ∨ t + k ≤ a := by
  unfold dataRead dataSegAt at hv
  cases hd : p.data.find? (fun d => decide (d.base ≤ t) && decide (t + k ≤ d.base + d.bytes.length)) with
  | none => rw [hd] at hv; simp at hv
  | some d =>
    have hm := List.mem_of_find?_eq_some hd
    have hp := List.find?_some hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hreg, _⟩ := h d hm
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
    obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, _⟩, hro⟩⟩ := hreg
    simp only [Memory.accessible, Bool.and_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw.2 r hr with (h1 | h1) | h1
    · rw [hro] at h1; cases h1
    · omega
    · omega

theorem pe_empty (b : Nat → Nat) : parseHex b 0 = .error 0 := by
  unfold parseHex; simp

theorem pe_missing (b : Nat → Nat) (n : Nat) (hn : n ≠ 0) (h : n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) :
    parseHex b n = .error 1 := by
  unfold parseHex; rw [if_neg hn, if_pos h]

theorem pe_emptyNum (b : Nat → Nat) (n : Nat) (hn : n = 2) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) :
    parseHex b n = .error 2 := by
  subst hn; unfold parseHex
  have : ¬ (2 < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by decide), if_neg this, if_pos rfl]

theorem pe_lead (b : Nat → Nat) (n : Nat) (hn : 3 < n) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) (h2 : b 2 = 48) :
    parseHex b n = .error 3 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_pos ⟨hn, h2⟩]

theorem pe_big (b : Nat → Nat) (n : Nat) (hn : 66 < n) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88) (h2 : b 2 ≠ 48) :
    parseHex b n = .error 4 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_neg (by omega), if_pos hn]

open Classical in
theorem pe_body (b : Nat → Nat) (n : Nat) (hn : 3 ≤ n) (hn2 : n ≤ 66) (h0 : b 0 = 48) (h1 : b 1 = 120 ∨ b 1 = 88)
    (h2 : 3 < n → b 2 ≠ 48) :
    parseHex b n = if allHex b 2 n then Except.ok (hexSum b 2 (n - 2)) else Except.error 5 := by
  unfold parseHex
  have : ¬ (n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)) := by omega
  have h3 : ¬ (3 < n ∧ b 2 = 48) := fun ⟨a, c⟩ => h2 a c
  rw [if_neg (by omega), if_neg this, if_neg (by omega), if_neg h3, if_neg (by omega)]

/-- the address of the package variable (an `error` interface value) for each parse error -/
def errAddrOf (e : Nat) : Nat :=
  if e = 0 then 1792752 else if e = 1 then 1792784 else if e = 2 then 1792800
  else if e = 3 then 1792816 else if e = 4 then 1792832 else 1792768

theorem errAddrOf_bounds (e : Nat) : 1792752 ≤ errAddrOf e ∧ errAddrOf e + 16 ≤ 1792848 := by
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
  (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.regs 0 = z ∧ s.regs 1 = hp ∧ s.regs 2 = len ∧
  Ptr32 s.mem z true ∧ Ptr s.mem hp len.toNat false ∧
  (∀ c, c < 256 → s.mem.readLE (1001813 + c) 1 = (hexNib c).getD 255) ∧ s.mem.accessible 1001813 256 false = true ∧
  (z.toNat + 32 ≤ 1001813 ∨ 1001813 + 256 ≤ z.toNat) ∧
  (s.sp.toNat - 24 + 48 ≤ 1001813 ∨ 1001813 + 256 ≤ s.sp.toNat - 24) ∧
  s.mem.accessible 1792752 96 false = true ∧ GuardOK s 0 ∧ StackOK s 24 24 ∧
  Disjoint z.toNat 32 hp.toNat len.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
  Disjoint hp.toNat len.toNat (s.sp.toNat - 24) 48 ∧ Disjoint z.toNat 32 1792752 96 ∧
  Disjoint 1792752 96 (s.sp.toNat - 24) 48 ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

def FromHexPost (z hp len : BitVec 64) (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
  s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
  (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v) ∧
  (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
      s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))

theorem hexSum_congr (b b' : Nat → Nat) (a : Nat) :
    ∀ n, (∀ k, a ≤ k → k < a + n → b k = b' k) → hexSum b a n = hexSum b' a n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [hexSum, hexDigit]
    rw [ih (fun k h1 h2 => h k h1 (by omega)), h (a + n) (by omega) (by omega)]

open Classical in
theorem parseHex_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) :
    parseHex b n = parseHex b' n := by
  have hall : allHex b 2 n ↔ allHex b' 2 n := by
    constructor
    · intro H k h1 h2; rw [← h k h2]; exact H k h1 h2
    · intro H k h1 h2; rw [h k h2]; exact H k h1 h2
  unfold parseHex
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · subst h1; simp
  have e0 : b 0 = b' 0 := h 0 (by omega)
  have e1 : b 1 = b' 1 := h 1 (by omega)
  by_cases h2 : n = 2
  · subst h2; simp [e0, e1]
  have e2 : b 2 = b' 2 := h 2 (by omega)
  simp only [e0, e1, e2, hall]
  rw [hexSum_congr b b' 2 (n - 2) (fun k h1 h2 => h k (by omega))]

open Classical in
theorem parseHex_error_lt (b : Nat → Nat) (n e : Nat) (h : parseHex b n = Except.error e) : e < 6 := by
  unfold parseHex at h
  by_cases h0 : n = 0
  · rw [if_pos h0] at h; cases h; decide
  rw [if_neg h0] at h
  by_cases h1 : n < 2 ∨ b 0 ≠ 48 ∨ (b 1 ≠ 120 ∧ b 1 ≠ 88)
  · rw [if_pos h1] at h; cases h; decide
  rw [if_neg h1] at h
  by_cases h2 : n = 2
  · rw [if_pos h2] at h; cases h; decide
  rw [if_neg h2] at h
  by_cases h3 : 3 < n ∧ b 2 = 48
  · rw [if_pos h3] at h; cases h; decide
  rw [if_neg h3] at h
  by_cases h4 : 66 < n
  · rw [if_pos h4] at h; cases h; decide
  rw [if_neg h4] at h
  by_cases h5 : allHex b 2 n
  · rw [if_pos h5] at h; cases h
  · rw [if_neg h5] at h; cases h; decide

theorem link_nil (p : Program) : p.link [] = p := by
  cases p; simp [Program.link]

theorem rr_mono {p : Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : ReachesRet p ret S Q) (hQ : ∀ s', Q s' → Q' s') : ReachesRet p ret S Q' := by
  obtain ⟨k, s', a, b, c⟩ := h
  exact ⟨k, s', a, b, hQ _ c⟩

theorem post_err (s s' : State) (z hp len : BitVec 64) (E : Nat)
    (hpar : parseHex (bytesAt s.mem hp.toNat) len.toNat = .error E)
    (hpc : s'.pc = s.regs 30) (hsp : s'.sp = s.sp) (h28 : s'.regs 28 = s.regs 28) (h29 : s'.regs 29 = s.regs 29)
    (h30 : s'.regs 30 = s.regs 30) (h18 : s'.regs 18 = s.regs 18)
    (hfr : MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)])
    (r0 : s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf E) 8))
    (r1 : s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf E + 8) 8)) : FromHexPost z hp len s s' := by
  refine ⟨hpc, hsp, h28, h29, h30, h18, hfr, ?_, ?_⟩
  · intro v hv; rw [hpar] at hv; cases hv
  · intro e he; rw [hpar] at he; cases he; exact ⟨r0, r1⟩

theorem post_of_loopQ (s s' : State) (z hp len : BitVec 64) (hn3 : 3 ≤ len.toNat) (hn66 : len.toNat ≤ 66)
    (h0 : bytesAt s.mem hp.toNat 0 = 48) (h1 : bytesAt s.mem hp.toNat 1 = 120 ∨ bytesAt s.mem hp.toNat 1 = 88)
    (h2 : 3 < len.toNat → bytesAt s.mem hp.toNat 2 ≠ 48) (hq : LoopQ s z hp len s') :
    FromHexPost z hp len s s' := by
  obtain ⟨hpc, hsp, h28, h29, h30, h18, hfr, hres⟩ := hq
  refine ⟨hpc, hsp, h28, h29, h30, h18, hfr, ?_, ?_⟩
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
      rw [val256_limbs, l0, l1, l2, l3, ht]
      simp only [hexW, Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one, Nat.reducePow, Nat.reduceMul]
      omega
    · rw [if_neg hnall] at hv; cases hv
  · intro e he
    rw [pe_body _ _ hn3 hn66 h0 h1 h2] at he
    rcases hres with ⟨r0, r1, hall, hl⟩ | ⟨r0, r1, hnall⟩
    · rw [if_pos hall] at he; cases he
    · rw [if_neg hnall] at he; cases he; exact ⟨r0, r1⟩

set_option maxHeartbeats 16000000 in
theorem fromHex_sum (impl : List Segment) (z hp len : BitVec 64) :
    Summary (Extracted.program.link impl) fh (FromHexPre z hp len) (FromHexPost z hp len) := by
  intro s hpc ⟨h30a, h30b, hz0, hp0, hl0, ⟨hz, hz'⟩, ⟨hs, hs'⟩, htab0, hSt0, hzt, hst, herr, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩,
    hdzh, hdzs, hdhs, hdzg, hdgs, hnn⟩
  subst hz0 hp0 hl0
  simp only [Disjoint] at hdzh hdzs hdhs hdzg hdgs
  have hn1 : s.mem.readLE 1792752 8 ≠ 0 := hnn 0 (by decide)
  have hn2 : s.mem.readLE 1792768 8 ≠ 0 := hnn 5 (by decide)
  have hn3 : s.mem.readLE 1792784 8 ≠ 0 := hnn 1 (by decide)
  have hn4 : s.mem.readLE 1792800 8 ≠ 0 := hnn 2 (by decide)
  have hn5 : s.mem.readLE 1792816 8 ≠ 0 := hnn 3 (by decide)
  have hn6 : s.mem.readLE 1792832 8 ≠ 0 := hnn 4 (by decide)
  have hb0 : s.mem.readLE (s.regs 1).toNat 1 < 256 := by simpa using Memory.readLE_lt s.mem (s.regs 1).toNat 1
  have hb1 : s.mem.readLE ((s.regs 1).toNat + 1) 1 < 256 := by simpa using Memory.readLE_lt s.mem ((s.regs 1).toNat + 1) 1
  have hb2 : s.mem.readLE ((s.regs 1).toNat + 2) 1 < 256 := by simpa using Memory.readLE_lt s.mem ((s.regs 1).toNat + 2) 1
  have e0 : bytesAt s.mem (s.regs 1).toNat 0 = s.mem.readLE (s.regs 1).toNat 1 := rfl
  have e1 : bytesAt s.mem (s.regs 1).toNat 1 = s.mem.readLE ((s.regs 1).toNat + 1) 1 := rfl
  have e2 : bytesAt s.mem (s.regs 1).toNat 2 = s.mem.readLE ((s.regs 1).toNat + 2) 1 := rfl
  janus_run until [innerHead]
  all_goals (try simp only [sw32 _ hb0, sw32 _ hb1, sw32 _ hb2] at *)
  all_goals first
    | (have hpar : parseHex (bytesAt s.mem (s.regs 1).toNat) (s.regs 2).toNat = Except.error 0 := by
         have h : (s.regs 2).toNat = 0 := by omega
         rw [h]; exact pe_empty _
       exact post_err _ _ _ _ _ _ hpar rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
         (by simp [setReg_apply]) (by janus_frame) (by simp [errAddrOf, setReg_apply]) (by simp [errAddrOf, setReg_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 1).toNat) (s.regs 2).toNat = Except.error 1 := pe_missing _ _ (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
         (by simp [setReg_apply]) (by janus_frame) (by simp [errAddrOf, setReg_apply]) (by simp [errAddrOf, setReg_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 1).toNat) (s.regs 2).toNat = Except.error 2 := pe_emptyNum _ _ (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
         (by simp [setReg_apply]) (by janus_frame) (by simp [errAddrOf, setReg_apply]) (by simp [errAddrOf, setReg_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 1).toNat) (s.regs 2).toNat = Except.error 3 := pe_lead _ _ (by omega) (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
         (by simp [setReg_apply]) (by janus_frame) (by simp [errAddrOf, setReg_apply]) (by simp [errAddrOf, setReg_apply]))
    | (have hpar : parseHex (bytesAt s.mem (s.regs 1).toNat) (s.regs 2).toNat = Except.error 4 := pe_big _ _ (by omega) (by omega) (by omega) (by omega)
       exact post_err _ _ _ _ _ _ hpar rfl rfl (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
         (by simp [setReg_apply]) (by janus_frame) (by simp [errAddrOf, setReg_apply]) (by simp [errAddrOf, setReg_apply]))
    | skip
  all_goals
    refine rr_mono (loop impl s (s.regs 0) (s.regs 1) (s.regs 2) (by omega) (by omega) h30a h30b hz' hs' hs hdzh (by omega)
           (by omega) hzt hdzg (by omega) (by omega) (by omega) hal
           (17 * (3 - 0) + ((s.regs 2).toNat - hexEnd (s.regs 2).toNat 1)) _ 0 (s.regs 2).toNat
           (hexEnd (s.regs 2).toNat 1) (hexEnd (s.regs 2).toNat 1) rfl (by omega) (by unfold hexEnd; omega) rfl
           (by unfold hexEnd; omega) (by omega) (by unfold hexEnd; omega) (by unfold hexEnd; omega) (Nat.le_refl _)
           (by unfold hexEnd; omega) rfl ?h0 ?h1 ?h3 ?h4 ?h2 ?h6 ?h5 ?hsp ?h28 ?h18 ?h29 ?h30 (allHex_nil _ _) (allHex_nil _ _)
           ?hlimbs ?hfr ?hlr ?hfp ?htab hw hz hs hSt0 herr) (fun s' hq => post_of_loopQ s s' _ _ _ (by omega) (by omega) (by omega)
           (by omega) (by omega) hq)
    case h0 => simp [setReg_apply]
    case h1 => simp [setReg_apply]
    case h3 => simp [setReg_apply]
    case h4 => simp [setReg_apply]
    case h2 => simp [setReg_apply]
    case h28 => simp [setReg_apply]
    case h18 => simp [setReg_apply]
    case h29 => simp [setReg_apply]
    case h30 => simp [setReg_apply]
    case hsp => dsimp only; rw [sp_sub16 _ (by omega)]; omega
    case hfr => janus_frame
    case h6 =>
      simp [setReg_apply]
      have ht := toInt_sub16' (s.regs 2) (by omega)
      first
      | (rw [ofNat_sub16' (s.regs 2) (by omega)]; congr 1; unfold hexEnd; omega)
      | (have h : hexEnd (s.regs 2).toNat 1 = 2 := by unfold hexEnd; omega
         rw [h])
    case h5 =>
      simp [setReg_apply]
      have ht := toInt_sub16' (s.regs 2) (by omega)
      first
      | (rw [ofNat_sub16' (s.regs 2) (by omega)]; congr 1; unfold hexEnd; omega)
      | (have h : hexEnd (s.regs 2).toNat 1 = 2 := by unfold hexEnd; omega
         rw [h])
    case hlimbs =>
      intro j hj
      dsimp only
      rw [zero_read _ _ j hj]
      simp [hexSum]
    case hlr =>
      dsimp only
      rw [sp_sub16 _ (by omega)]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h8]; exact Nat.mod_eq_of_lt (s.regs 30).isLt
    case hfp =>
      dsimp only
      rw [sp_sub16 _ (by omega), show BitVec.toNat s.sp - 16 - 8 = BitVec.toNat s.sp - 24 by omega]
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      have h8 : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      rw [h8]; exact Nat.mod_eq_of_lt (s.regs 29).isLt
    case htab =>
      intro c hc
      dsimp only
      simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self]
      exact htab0 c hc


end Fv256.Arm64.SetFromHexLoops
