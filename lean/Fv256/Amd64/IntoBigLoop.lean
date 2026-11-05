import Fv256.Amd64.IntoBigDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Amd64.IntoBig

/-- The head of the normalization loop of the allocating path: `test %rcx,%rcx` (`IntoBig+0x100`). -/
abbrev pcLoopHead : Nat := Extracted.entry + 0x100
/-- Its exit: `cmp $4,%rcx` (`IntoBig+0x10f`). -/
abbrev pcLoopExit : Nat := Extracted.entry + 0x10f

theorem sub1 (k : Nat) (hk : k < 2 ^ 63) : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- The normalization loop `for len > 0 && words[len-1] == 0 { len-- }` of `IntoBig`, by induction on the length `k`. -/
theorem normloop (impl : List Amd64.Segment) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret) (Q : Amd64.Outcome → Prop) (A : Nat) (limb : Nat → Nat)
    (hA48 : A + 32 ≤ 2 ^ 48) :
    ∀ k, k ≤ 4 → ∀ S : State, S.rip = BitVec.ofNat 64 pcLoopHead → S.regs 0 = BitVec.ofNat 64 A →
      S.regs 1 = BitVec.ofNat 64 k → S.mem.accessible A 32 false = true →
      (∀ i, i < 4 → S.mem.readLE (A + 8 * i) 8 = limb i) →
      (∀ S2 : State, ∀ len, len ≤ k → (len = 0 ∨ limb (len - 1) ≠ 0) → (∀ i, len ≤ i → i < k → limb i = 0) →
        S2.rip = BitVec.ofNat 64 pcLoopExit → S2.regs 0 = S.regs 0 → S2.regs 1 = BitVec.ofNat 64 len →
        S2.regs 4 = S.regs 4 → S2.mem = S.mem → (∀ r, r ≠ 1 → r ≠ 2 → S2.regs r = S.regs r) →
        Reaches ((Extracted.program.link impl).withExit ret) S2 Q) →
      Reaches ((Extracted.program.link impl).withExit ret) S Q := by
  intro k
  induction k with
  | zero =>
    intro hk S hpc h0 h1 hacc hlimb hcont
    janus64_run until [pcLoopExit]
    exact hcont _ 0 (Nat.le_refl _) (Or.inl rfl) (fun i h1 h2 => absurd h2 (by omega)) rfl rfl h1 rfl rfl
      (fun r _ _ => rfl)
  | succ k ih =>
    intro hk S hpc h0 h1 hacc hlimb hcont
    have hacck : S.mem.accessible (A + 8 * k) 8 false = true :=
      Janus.Arm64.Memory.accessible_sub S.mem hacc (Or.inl rfl) (by omega) (by omega)
    have hlk : limb k < 2 ^ 64 := by
      rw [← hlimb k (by omega)]; simpa using Janus.Arm64.Memory.readLE_lt S.mem (A + 8 * k) 8
    have hmsb : (BitVec.ofNat 64 (k + 1)).msb = false := by
      rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega
    have hrd : S.mem.readLE (A + (k + 1) * 8 - 8) 8 = limb k := by
      rw [← hlimb k (by omega)]; congr 1; omega
    janus64_run until [pcLoopHead, pcLoopExit]
    · exact absurd hbr (by rw [hmsb]; simp)
    · have hz0 : limb k = 0 := hbr
      refine ih (by omega) _ rfl (by simp [setRegF_apply, h0]) (by simp [setRegF_apply]; exact sub1 k (by omega)) hacc hlimb ?_
      intro S2 len hl hn hz hp hr0 hr1 hsp hm hr
      refine hcont S2 len (by omega) hn ?_ hp (by rw [hr0]; simp [setRegF_apply]) hr1 hsp hm
        (fun r a b => by rw [hr r a b]; simp [setRegF_apply, a, b])
      intro i hi1 hi2
      by_cases hik : i < k
      · exact hz i hi1 hik
      · have : i = k := by omega
        subst this; exact hz0
    · refine hcont _ (k + 1) (Nat.le_refl _) (Or.inr ?_) (fun i h1 h2 => absurd h2 (by omega)) rfl
        (by simp [setRegF_apply]) (by simp [setRegF_apply, h1]) rfl rfl (fun r a b => by simp [setRegF_apply, a, b])
      show limb k ≠ 0
      intro h; exact hbr h

end Fv256.Amd64.IntoBig
