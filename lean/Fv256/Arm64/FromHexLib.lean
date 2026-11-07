import Fv256.Arm64.FromHexProg
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.HexLemmas

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Fv256.C

namespace Fv256.Arm64.FromHexLib

abbrev fh : Nat := segAddr Fv256.Arm64.FromHexProg.program "github.com/holiman/uint256.(*Int).fromHex"
abbrev outerHead : Nat := fh + 0x10c

/-- address of the sentinel error variable loaded by the ADRP/ADD pair at word index `i` of `fromHex` -/
def errAddr (i : Nat) : Nat :=
  adrpLdTarget (fh + 4 * i) (segWord Fv256.Arm64.FromHexProg.program "github.com/holiman/uint256.(*Int).fromHex" i)
    (segWord Fv256.Arm64.FromHexProg.program "github.com/holiman/uint256.(*Int).fromHex" (i + 1)) 0

/-- the six sentinel error variables (`ErrEmptyString`, `ErrSyntax`, `ErrMissingPrefix`, `ErrEmptyNumber`, `ErrLeadingZero`, `ErrBig256Range`)
are consecutive 16-byte interface values at these addresses (`.data`, not copied by the extraction: the precondition provides them). -/
def eEmpty : Nat := 1792784
def eSyn : Nat := 1792800
def ePrefix : Nat := 1792816
def eNum : Nat := 1792832
def eLead : Nat := 1792848
def eBig : Nat := 1792864

theorem err_addrs : errAddr 8 = eEmpty ∧ errAddr 22 = ePrefix ∧ errAddr 30 = eNum ∧ errAddr 39 = eLead ∧ errAddr 54 = eBig ∧
    errAddr 98 = eSyn := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide


abbrev innerHead : Nat := fh + 0x144
abbrev tbl : Nat := 1002789

/-- postcondition of the digit loop (relative to the entry state `s` of `fromHex`) -/
def LoopQ (s : State) (z hp len : BitVec 64) (s' : State) : Prop :=
  s'.pc = s.regs regLR ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
  s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
  ((s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ allHex (bytesAt s.mem hp.toNat) 2 len.toNat ∧
      ∀ j, j < 4 → s'.mem.readLE (z.toNat + 8 * j) 8 = hexLimb (bytesAt s.mem hp.toNat) len.toNat j) ∨
   (s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE 1792800 8) ∧ s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE 1792808 8) ∧
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
    (hzt : z.toNat + 32 ≤ 1002789 ∨ 1002789 + 256 ≤ z.toNat)
    (hgz : z.toNat + 32 ≤ 1792784 ∨ 1792880 ≤ z.toNat)
    (hgs : s.sp.toNat + 24 ≤ 1792784 ∨ 1792880 ≤ s.sp.toNat - 24)
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
      (∀ c, c < 256 → S.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255) →
      s.mem.accessible (s.sp.toNat - 24) 48 true = true → s.mem.accessible z.toNat 32 true = true →
      s.mem.accessible hp.toNat len.toNat false = true → s.mem.accessible 1002789 256 false = true →
      s.mem.accessible 1792784 96 false = true →
      ReachesRet (Fv256.Arm64.FromHexProg.program.link impl) (s.regs regLR) S (LoopQ s z hp len) := by
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


/-- the address of the package variable (an `error` interface value) for each parse error -/
def errAddrOf (e : Nat) : Nat :=
  if e = 0 then 1792784 else if e = 1 then 1792816 else if e = 2 then 1792832
  else if e = 3 then 1792848 else if e = 4 then 1792864 else 1792800

theorem errAddrOf_bounds (e : Nat) : 1792784 ≤ errAddrOf e ∧ errAddrOf e + 16 ≤ 1792880 := by
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
  (∀ c, c < 256 → s.mem.readLE (1002789 + c) 1 = (hexNib c).getD 255) ∧ s.mem.accessible 1002789 256 false = true ∧
  (z.toNat + 32 ≤ 1002789 ∨ 1002789 + 256 ≤ z.toNat) ∧
  (s.sp.toNat - 24 + 48 ≤ 1002789 ∨ 1002789 + 256 ≤ s.sp.toNat - 24) ∧
  s.mem.accessible 1792784 96 false = true ∧ GuardOK s 0 ∧ StackOK s 24 24 ∧
  Disjoint z.toNat 32 hp.toNat len.toNat ∧ Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧
  Disjoint hp.toNat len.toNat (s.sp.toNat - 24) 48 ∧ Disjoint z.toNat 32 1792784 96 ∧
  Disjoint 1792784 96 (s.sp.toNat - 24) 48 ∧ (∀ e, e < 6 → s.mem.readLE (errAddrOf e) 8 ≠ 0)

def FromHexPost (z hp len : BitVec 64) (s s' : State) : Prop :=
  s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
  s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
  MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24), (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
  (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem z.toNat = v) ∧
  (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
      s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
      s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))

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
    Summary (Fv256.Arm64.FromHexProg.program.link impl) fh (FromHexPre z hp len) (FromHexPost z hp len) := by
  intro s hpc ⟨h30a, h30b, hz0, hp0, hl0, ⟨hz, hz'⟩, ⟨hs, hs'⟩, htab0, hSt0, hzt, hst, herr, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩,
    hdzh, hdzs, hdhs, hdzg, hdgs, hnn⟩
  subst hz0 hp0 hl0
  simp only [Disjoint] at hdzh hdzs hdhs hdzg hdgs
  have hn1 : s.mem.readLE 1792784 8 ≠ 0 := hnn 0 (by decide)
  have hn2 : s.mem.readLE 1792800 8 ≠ 0 := hnn 5 (by decide)
  have hn3 : s.mem.readLE 1792816 8 ≠ 0 := hnn 1 (by decide)
  have hn4 : s.mem.readLE 1792832 8 ≠ 0 := hnn 2 (by decide)
  have hn5 : s.mem.readLE 1792848 8 ≠ 0 := hnn 3 (by decide)
  have hn6 : s.mem.readLE 1792864 8 ≠ 0 := hnn 4 (by decide)
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



end Fv256.Arm64.FromHexLib
