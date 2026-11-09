import Janus
import Fv256.Proofs.Arm64.SfdTopSpec
import Fv256.Proofs.Arm64.UnmarshalSpec

/-!
# Facts about the result of `runtime.slicebytetostring(buf, ptr, n)` for a stack buffer `buf` (Extracted-free)

Where a non-empty result lives (`StrAt`) and what that gives for the callee window `[lo, hi3)` of the next call
(`hi3 ≤ buf`), the interface model's private ranges and the receiver `[z, z+32)`.
-/

open Janus Janus.Contracts Janus.Arm64 Janus.Tactic

namespace Fv256.Arm64.SbtsFacts

/-- the live additions of the contract, simplified -/
theorem adds_eq (c : Prop) [Decidable c] (n r0 : Nat) :
    (((if c then (if n = 0 then [] else [(r0, r0 + n)]) else []) ++
      (if c then [] else if n = 0 then [] else [(r0, r0 + n)])) : List (Nat × Nat)) =
    (if n = 0 then [] else [(r0, r0 + n)]) := by
  by_cases hc : c <;> by_cases hn : n = 0 <;> simp [hc, hn]

theorem loc {rt priv : List (Nat × Nat)} {buf st ptr n r0 lo hi hi3 z : Nat} {m0 : Janus.Arm64.Memory}
    {L : List (Nat × Nat)} (h : StrAt rt buf st ptr n r0 m0) (hn : 0 < n)
    (hb1 : lo ≤ buf) (hb2 : buf + 32 ≤ hi) (hh3 : hi3 ≤ buf) (hh3' : hi3 ≤ hi)
    (hwrt : Outside lo (hi - lo) rt) (hwp : Outside lo (hi - lo) priv)
    (hpwf : ∀ r ∈ priv, r.1 ≤ r.2) (hprt : ∀ r ∈ priv, Outside r.1 (r.2 - r.1) rt)
    (hstW : Outside st 2048 [(lo, hi)]) (hstP : Outside st 2048 priv) (hstZ : Outside st 2048 [(z, z + 32)])
    (hzw : z + 32 ≤ lo ∨ hi ≤ z) (hzL : Outside z 32 rt ∨ InRanges z 32 L)
    (hbuf : buf ≠ 0) (hfr : 32 < n → ApartAll r0 n L) :
    Outside r0 n [(lo, hi3)] ∧ Outside r0 n priv ∧ (r0 + n ≤ z ∨ z + 32 ≤ r0) := by
  rcases h with h0 | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, r, hr, hr1, hr2⟩
  · omega
  · have hb := Janus.Arm64.Memory.readLE_lt m0 ptr 1
    simp only [Nat.reducePow, Nat.pow_one] at hb
    have hs : r0 + n ≤ st + 2048 ∧ st ≤ r0 := by omega
    have := hstZ
    simp only [outside_cons, outside_nil, and_true] at this
    refine ⟨Outside.of_sub (rs := [(lo, hi3)]) ?_ hs.2 hs.1, Outside.of_sub hstP hs.2 hs.1, ?_⟩
    · simp only [outside_cons, outside_nil, and_true] at hstW ⊢; omega
    · omega
  · subst h4
    refine ⟨?_, Outside.of_sub hwp hb1 (by omega), by omega⟩
    simp only [outside_cons, outside_nil, and_true]; omega
  · have hin : InRanges r0 n rt := ⟨r, hr, hr1, hr2⟩
    have hw := MemFrame.outside_mem hwrt hr
    have hwin : r0 + n ≤ lo ∨ hi ≤ r0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [outside_cons, outside_nil, and_true]; omega
    · exact Fv256.Arm64.UnmarshalSpec.outside_of_in hin priv hpwf hprt
    · rcases hzL with hz | hz
      · have := InRanges.apart hin hz
        unfold Apart at this; omega
      · have := (hfr (by omega)).apart_of_inRanges hz
        omega

end Fv256.Arm64.SbtsFacts
