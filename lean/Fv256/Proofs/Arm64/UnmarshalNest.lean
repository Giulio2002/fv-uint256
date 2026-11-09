import Fv256.Proofs.Arm64.UnmarshalKeepN
import Fv256.Proofs.Arm64.UnmarshalSpecJ

/-!
# `UnmarshalText` called from `UnmarshalJSON` (arm64, Extracted-free): the call state `T` and the transfers to it
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.UnmarshalSpec Fv256.Arm64.UnmarshalDecN Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalHex

namespace Fv256.Arm64.UnmarshalNest

theorem exists_T (s : State) (MJ : Janus.Arm64.Memory) (z pI' nI' : BitVec 64) (sp' : BitVec 64) :
    ∃ T : State, T.regs 0 = z ∧ T.regs 1 = pI' ∧ T.regs 2 = nI' ∧ T.sp = sp' ∧ T.regs 28 = s.regs 28 ∧ T.mem = MJ :=
  ⟨{ s with regs := fun i => if i = 0 then z else if i = 1 then pI' else if i = 2 then nI' else s.regs i, sp := sp', mem := MJ },
    by simp, by simp, by simp, rfl, by simp, rfl⟩

theorem sbpost_nest {R : RtInv} {st b : Nat} {L : List (Nat × Nat)} {sp : Nat} {Sj T : State} {p n : Nat} {pI' nI' r0 r1 : BitVec 64}
    {M0 m : Janus.Arm64.Memory} {buf : Nat}
    (hp' : pI'.toNat = p) (hn' : nI'.toNat = n) (hT28 : T.regs 28 = Sj.regs 28)
    (hbytes : strBytes T.mem p n = strBytes Sj.mem p n)
    {q : Nat} (hq : q = sp - 112)
    (hmf : MemFrame M0 m (R.rt ++ [(q - 4096, q - 8), (q + 8, q + 8 + 24)] ++
      (if buf = 0 then [] else [(buf, buf + 32)])))
    (hsoa : (r1.toNat = (strBytes Sj.mem p n).length ∧ r0.toNat + r1.toNat ≤ 2 ^ 48 ∧
      (0 < r1.toNat → Sj.mem.accessible r0.toNat r1.toNat false = true) ∧ strBytes m r0.toNat r1.toNat = strBytes Sj.mem p n) ∧
      StrAt R.rt buf st p r1.toNat r0.toNat M0)
    (hacc : ∀ x y, T.mem.accessible x y false = Sj.mem.accessible x y false)
    (hlf : LiveFrame M0 m L (if buf = 0 then [] else [(buf, buf + 32)]))
    (hfr : FreshFrom (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
        (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) L)
    (hinv : R.inv (b - roundupsize n true)
      (L ++ ((if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)])))
      (Sj.regs 28).toNat (view R.rt (L ++ ((if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then
          (if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]) else []) ++
        (if 2 ≤ r1.toNat ∧ (buf = 0 ∨ 32 < r1.toNat) then []
         else if r1.toNat = 0 then [] else [(r0.toNat, r0.toNat + r1.toNat)]))) m)) :
    SbPost R st b L sp T pI' nI' r0 r1 M0 m buf := by
  subst hp' hn' hq
  refine ⟨hmf, ?_, hlf, hfr, ?_⟩
  · obtain ⟨⟨a1, a2, a3, a4⟩, a5⟩ := hsoa
    refine ⟨⟨by rw [hbytes]; exact a1, a2, fun h => by rw [hacc]; exact a3 h, by rw [hbytes]; exact a4⟩, a5⟩
  · rw [hT28]; exact hinv

theorem hexEnv_frame {R : RtInv} {lo hi : Nat} {z : BitVec 64} {s T : State} (henv : HexEnv R lo hi z s)
    (hF : MemFrame s.mem T.mem [(lo, hi)]) : HexEnv R lo hi z T := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := henv
  have t3' := t3
  have t6' := t6
  simp only [outside_cons, outside_nil, and_true] at t3' t6'
  refine ⟨fun c hc => ?_, by rw [hF.accessible]; exact t2, t3, t4, by rw [hF.accessible]; exact t5, t6, t7, fun e he => ?_⟩
  · rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact t1 c hc
  · have hb := errAddrOf_bounds e
    rw [hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)]; exact t8 e he

end Fv256.Arm64.UnmarshalNest
