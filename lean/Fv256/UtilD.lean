import Janus
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB

open Lean Elab Tactic Meta in
/-- clear every hypothesis that mentions an explicit machine-state literal (the callee summary's register and `pc` equalities after
a call): only the executor needs them, and they make `simp at *` and `generalize at *` very slow -/
elab "clear_states" : tactic => do
  let mut g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isAppOf ``Janus.Arm64.State.mk).isSome then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

open Lean Elab Tactic Meta in
/-- same for the amd64 machine state -/
elab "clear_states64" : tactic => do
  let mut g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isAppOf ``Janus.Amd64.State.mk).isSome then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

open Lean Elab Tactic Meta in
/-- `grab_lsh h`: name (as `h`) the first local hypothesis whose type mentions `Fv256.Spec.lsh` (the callee's anonymous
post-condition conjunct after a `janus_run calls [..]`) -/
elab "grab_lsh " n:ident : tactic => do
  let g ← getMainGoal
  for d in (← g.getDecl).lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if (ty.find? fun e => e.isConstOf ``Fv256.Spec.lsh).isSome then
      let g' ← g.withContext do
        let (_, g') ← g.note n.getId (mkFVar d.fvarId) ty
        pure g'
      replaceMainGoal [g']
      return
  throwError "grab_lsh: no hypothesis mentions Spec.lsh"

open Lean Elab Tactic Meta in
/-- `fast_assm t`: close/produce `t` from a hypothesis whose type is *syntactically* `t` (no unification, cheap on huge contexts) -/
elab "fast_assm " t:term : tactic => do
  let g ← getMainGoal
  let e ← g.withContext (Term.withSynthesize (Term.elabTerm t none))
  let ty ← instantiateMVars e
  g.withContext do
    for d in (← g.getDecl).lctx do
      if d.isImplementationDetail then continue
      if (← withReducible (isDefEq (← instantiateMVars d.type) ty)) then
        g.assign (mkFVar d.fvarId)
        replaceMainGoal []
        return
  throwError "fast_assm: no match for {ty}; hyps: {(← g.getDecl).lctx.foldl (fun (a : List MessageData) d => if d.isImplementationDetail then a else a ++ [m!"{d.userName} : {d.type}"]) []}"

open Lean Elab Tactic in
/-- profiling aid: run `t`, log how long it took and whether it failed (rethrows) -/
elab "timed " s:str t:tacticSeq : tactic => do
  let t0 ← IO.monoMsNow
  try
    evalTactic t
    logInfo m!"timed {s.getString}: ok {(← IO.monoMsNow) - t0} ms"
  catch e =>
    logInfo m!"timed {s.getString}: FAIL {(← IO.monoMsNow) - t0} ms"
    throw e

namespace Fv256.D

theorem f64_bits (q r t Y y0 y1 y2 y3 : Nat) (ht1 : 12 ≤ t) (ht2 : t ≤ 203) (hr : r < 2 ^ t) (hq : q < 2 ^ 52)
    (hY : Y = q * 2 ^ 204 + r * 2 ^ (204 - t))
    (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = Y) :
    y3 / 4096 = q ∧
    (2048 ≤ y3 % 4096 ↔ 2 ^ (t - 1) ≤ r) ∧
    ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ r % 2 ^ (t - 1) ≠ 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hh : 2 ^ s * 2 ^ (204 - (s + 1)) = 2 ^ 203 := by
    rw [← Nat.pow_add]; congr 1; omega
  have hr2 : r < 2 * 2 ^ s := by rw [Nat.pow_succ] at hr; omega
  clear hr
  generalize 2 ^ s = h at *
  generalize 2 ^ (204 - (s + 1)) = Pm at *
  have hp : 0 < Pm := by
    rcases Nat.eq_zero_or_pos Pm with h | h
    · subst h; simp at hh
    · exact h
  have hpos : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h' | h'
    · subst h'; simp at hh
    · exact h'
  have hu : r * Pm < 2 ^ 204 := by
    have : r * Pm < 2 * h * Pm := Nat.mul_lt_mul_of_pos_right hr2 hp
    have e : 2 * h * Pm = 2 ^ 204 := by rw [Nat.mul_assoc, hh]
    omega
  generalize hU : r * Pm = u at *
  have e3 : y3 = Y / 2 ^ 192 := by omega
  have eY : y3 / 4096 = q ∧ y3 % 4096 = u / 2 ^ 192 := by omega
  refine ⟨eY.1, ?_, ?_⟩
  · rw [eY.2]
    have : 2048 ≤ u / 2 ^ 192 ↔ 2 ^ 203 ≤ u := by omega
    rw [this, ← hh, ← hU]
    exact Nat.mul_le_mul_right_iff hp
  · have : (y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ↔ u % 2 ^ 203 ≠ 0 := by omega
    rw [this, ← hh, ← hU, Nat.mul_mod_mul_right]
    constructor
    · intro hne hz; apply hne; rw [hz]; simp
    · intro hne hz; apply hne
      rcases Nat.mul_eq_zero.1 hz with h | h
      · exact h
      · omega

set_option maxRecDepth 100000 in
open Janus.Float in
theorem f64_nearest (V bl y0 y1 y2 y3 : Nat) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V) (hbl : Spec.bitLen V = bl)
    (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256) :
    Fv256.B.float64BitsNearest V =
      (if (if 2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)
          then y3 / 4096 + 1 else y3 / 4096) / 2 ^ 52 ≠ 0
        then (bl + 1023) * 2 ^ 52
        else (bl + 1022) * 2 ^ 52 +
          (if 2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)
            then y3 / 4096 + 1 else y3 / 4096)) := by
  have hV0 : V ≠ 0 := by have := Nat.two_pow_pos 64; omega
  obtain ⟨hb1, hb2⟩ := Util.bitLen_bounds V hV0
  rw [hbl] at hb1 hb2
  have hbl64 : 64 < bl := by
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ bl ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨L, rfl⟩ : ∃ L, bl = L + 1 := ⟨bl - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hb1
  have hL64 : 64 ≤ L := by omega
  have hL255 : L ≤ 255 := by
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 256 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = L - 52 := ⟨_, rfl⟩
  have ht12 : 12 ≤ t := by omega
  have ht203 : t ≤ 203 := by omega
  have hLt : L = t + 52 := by omega
  -- decomposition
  have h2L : 0 < 2 ^ t := Nat.two_pow_pos t
  have hWdef : V = 2 ^ L + V % 2 ^ L := by
    have : V / 2 ^ L = 1 := by
      apply Nat.le_antisymm
      · have : V / 2 ^ L < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos L)).2 (by rw [Nat.pow_succ] at hb2; omega)
        omega
      · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos L)).2 (by omega)
    have := Nat.div_add_mod V (2 ^ L)
    rw [‹V / 2 ^ L = 1›] at this
    omega
  have hWlt : V % 2 ^ L < 2 ^ L := Nat.mod_lt _ (Nat.two_pow_pos L)
  have hq : V % 2 ^ L / 2 ^ t < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul h2L, ← Nat.pow_add]; rw [show 52 + t = L by omega]; exact hWlt
  have hrW : V % 2 ^ L % 2 ^ t = V % 2 ^ t := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))
  have hk : V / 2 ^ t = 2 ^ 52 + V % 2 ^ L / 2 ^ t := by
    have e : 2 ^ L = 2 ^ 52 * 2 ^ t := by rw [← Nat.pow_add]; congr 1; omega
    have e5 : V = V % 2 ^ L + 2 ^ t * 2 ^ 52 := by omega
    calc V / 2 ^ t = (V % 2 ^ L + 2 ^ t * 2 ^ 52) / 2 ^ t := by rw [← e5]
      _ = _ := by rw [Nat.add_mul_div_left _ _ h2L]; omega
  have hr : V % 2 ^ t < 2 ^ t := Nat.mod_lt _ h2L
  have hY : V * 2 ^ (257 - (L + 1)) % 2 ^ 256 = V % 2 ^ L / 2 ^ t * 2 ^ 204 + V % 2 ^ t * 2 ^ (204 - t) := by
    have e1 : 257 - (L + 1) = 256 - L := by omega
    rw [e1]
    have e2 : V % 2 ^ L * 2 ^ (256 - L) < 2 ^ 256 := by
      calc V % 2 ^ L * 2 ^ (256 - L) < 2 ^ L * 2 ^ (256 - L) := Nat.mul_lt_mul_of_pos_right hWlt (Nat.two_pow_pos _)
        _ = 2 ^ 256 := by rw [← Nat.pow_add]; congr 1; omega
    have e3 : V * 2 ^ (256 - L) = 2 ^ 256 + V % 2 ^ L * 2 ^ (256 - L) := by
      calc V * 2 ^ (256 - L) = (2 ^ L + V % 2 ^ L) * 2 ^ (256 - L) := by rw [← hWdef]
        _ = _ := by rw [Nat.add_mul, ← Nat.pow_add, show L + (256 - L) = 256 by omega]
    rw [e3, Nat.add_mod_left, Nat.mod_eq_of_lt e2]
    have e4 : V % 2 ^ L = V % 2 ^ L / 2 ^ t * 2 ^ t + V % 2 ^ t := by
      have := Nat.div_add_mod (V % 2 ^ L) (2 ^ t)
      rw [hrW, Nat.mul_comm (2 ^ t)] at this; omega
    calc V % 2 ^ L * 2 ^ (256 - L) = (V % 2 ^ L / 2 ^ t * 2 ^ t + V % 2 ^ t) * 2 ^ (256 - L) := by rw [← e4]
      _ = _ := by rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, show t + (256 - L) = 204 by omega, show 256 - L = 204 - t by omega]
  have hbits := f64_bits (V % 2 ^ L / 2 ^ t) (V % 2 ^ t) t (V * 2 ^ (257 - (L + 1)) % 2 ^ 256) y0 y1 y2 y3 ht12 ht203 hr hq hY h0 h1 h2 h3 hy
  obtain ⟨hb_q, hb_rnd, hb_st⟩ := hbits
  have hR : (roundAt RM.rne false V 0 ((L : Int) - 52)).1 =
      (if roundUp RM.rne false (V / 2 ^ t) (V % 2 ^ t) t = true then V / 2 ^ t + 1 else V / 2 ^ t) := by
    unfold roundAt
    rw [if_neg (by omega)]
    have : ((L : Int) - 52 - 0).toNat = t := by omega
    simp only [this]
  unfold Fv256.B.float64BitsNearest
  rw [fromInt_b64_big .rne V L hb1 hb2 (by omega) (by omega), hR]
  have hh : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hhpos : 0 < 2 ^ (t - 1) := Nat.two_pow_pos _
  generalize 2 ^ (t - 1) = h at *
  have hmod : V % 2 ^ t % h = if h ≤ V % 2 ^ t then V % 2 ^ t - h else V % 2 ^ t := by
    split
    · rw [Nat.mod_eq_sub_mod ‹_›, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hRU : roundUp RM.rne false (V / 2 ^ t) (V % 2 ^ t) t = true ↔
      (2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)) := by
    unfold roundUp
    rw [hb_rnd, hb_st, hb_q, hk]
    simp only [Nat.add_mod_left, hmod]
    generalize V % 2 ^ t = r at *
    generalize V % 2 ^ L / 2 ^ t = q at *
    by_cases a : r = 0 <;> by_cases b : h ≤ r <;> simp [a, b] <;> omega
  unfold pack
  rw [Janus.Float.b64_fbits]
  have e53 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by decide
  have hk' : V / 2 ^ t = 2 ^ 52 + y3 / 4096 := by rw [hk, hb_q]
  rw [e53, hk']
  rw [hk'] at hRU
  by_cases hC : (2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1))
  · simp only [if_pos (hRU.2 hC), if_pos hC, Bool.false_eq_true, ite_false]
    split <;> split <;> omega
  · simp only [if_neg (fun h => hC (hRU.1 h)), if_neg hC, Bool.false_eq_true, ite_false]
    split <;> split <;> omega


theorem or_add (a b k : Nat) (ha : a < 2 ^ k) : (a ||| b * 2 ^ k) = a + b * 2 ^ k := by
  have := Nat.two_pow_add_eq_or_of_lt ha b
  rw [Nat.or_comm, Nat.mul_comm b, Nat.add_comm, this]

theorem rot12 (y : Nat) (hy : y < 2 ^ 64) :
    ((BitVec.ofNat 64 y).rotateRight 12 &&& 18446744073709551615#64 &&& 4503599627370495#64).toNat = y / 4096 := by
  simp only [BitVec.toNat_and, BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy, Nat.reduceMod]
  have e1 : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := by decide
  have e2 : (4503599627370495 : Nat) = 2 ^ 52 - 1 := by decide
  rw [e1, e2, Nat.mod_eq_of_lt (by decide : 2 ^ 64 - 1 < 2 ^ 64), Nat.mod_eq_of_lt (by decide : 2 ^ 52 - 1 < 2 ^ 64), Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod]
  have h3 : y <<< (64 - 12) % 2 ^ 64 % 2 ^ 52 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    show y * 2 ^ 52 % 2 ^ 52 = 0
    simp
  have h4 : (y >>> 12) < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have h5 : (y >>> 12 ||| y <<< (64 - 12) % 2 ^ 64) < 2 ^ 64 :=
    Nat.or_lt_two_pow h4 (Nat.mod_lt _ (by omega))
  rw [Nat.mod_eq_of_lt h5, Nat.or_mod_two_pow, h3, Nat.or_zero, Nat.shiftRight_eq_div_pow]
  show y / 2 ^ 12 % 2 ^ 52 = y / 4096
  apply Nat.mod_eq_of_lt; omega

theorem rot52 (v : BitVec 64) : (v.rotateRight 52).toNat % 4096 = v.toNat / 2 ^ 52 := by
  have hv := v.isLt
  rw [BitVec.toNat_rotateRight, show (4096 : Nat) = 2 ^ 12 by decide]
  have h3 : v.toNat <<< (64 - 52 % 64) % 2 ^ 64 % 2 ^ 12 = 0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)), Nat.shiftLeft_eq]
    simp
  rw [Nat.or_mod_two_pow, h3, Nat.or_zero, Nat.shiftRight_eq_div_pow]
  show v.toNat / 2 ^ (52 % 64) % 2 ^ 12 = v.toNat / 2 ^ 52
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  simpa using hv


theorem form_val (F e : BitVec 64) (hF : F.toNat ≤ 2 ^ 52) (he : e.toNat ≤ 256) :
    ((if (F.rotateRight 52).toNat % 4096 = 0 then F else 0#64).toNat |||
        4503599627370496 * (if (F.rotateRight 52).toNat % 4096 = 0 then e + 1022#64 else e + 1023#64).toNat % 18446744073709551616)
      % 18446744073709551616 % 2 ^ 128 % 2 ^ 64 =
    if F.toNat / 2 ^ 52 ≠ 0 then (e.toNat + 1023) * 2 ^ 52 else (e.toNat + 1022) * 2 ^ 52 + F.toNat := by
  rw [rot52]
  have e1 : (e + 1022#64).toNat = e.toNat + 1022 := by
    rw [BitVec.toNat_add]; simp; omega
  have e2 : (e + 1023#64).toNat = e.toNat + 1023 := by
    rw [BitVec.toNat_add]; simp; omega
  by_cases c : F.toNat / 2 ^ 52 = 0
  · have hl : F.toNat < 2 ^ 52 := by
      rcases Nat.div_eq_zero_iff.1 c with h | h
      · exact absurd h (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
      · exact h
    rw [if_pos c, if_pos c, e1, if_neg (by simpa using c), Nat.mul_comm 4503599627370496, show (4503599627370496 : Nat) = 2 ^ 52 by decide]
    rw [Nat.mod_eq_of_lt (by omega : (e.toNat + 1022) * 2 ^ 52 < 2 ^ 64), or_add _ _ _ hl]
    rw [Nat.add_comm]
    repeat rw [Nat.mod_eq_of_lt (by omega)]
  · have h52 : F.toNat = 2 ^ 52 := by
      have : 2 ^ 52 ≤ F.toNat := by
        by_cases h : F.toNat < 2 ^ 52
        · exact absurd (Nat.div_eq_of_lt h) c
        · omega
      omega
    rw [if_neg c, if_neg c, e2, if_pos (by simpa using c)]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_or]
    rw [show (4503599627370496 : Nat) = 2 ^ 52 by decide, Nat.mul_comm]
    repeat rw [Nat.mod_eq_of_lt (by omega)]



/-- the machine's `frac = fraction >> 12` (as `LSR` is modelled) -/
abbrev fr (y3 : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 y3).rotateRight 12 &&& 18446744073709551615#64 &&& 4503599627370495#64

/-- the machine's final packing, as the executor shows it, for the register `F` (fraction, maybe rounded up) and exponent `e` -/
abbrev Form (F e : BitVec 64) : Nat :=
  ((if (F.rotateRight 52).toNat % 4096 = 0 then F else 0#64).toNat |||
        4503599627370496 * (if (F.rotateRight 52).toNat % 4096 = 0 then e + 1022#64 else e + 1023#64).toNat % 18446744073709551616)
      % 18446744073709551616 % 2 ^ 128 % 2 ^ 64

/-- round-to-nearest-even decision -/
abbrev Up (y0 y1 y2 y3 : Nat) : Prop :=
  2048 ≤ y3 % 4096 ∧ ((y3 % 2048 ≠ 0 ∨ y0 ≠ 0 ∨ y1 ≠ 0 ∨ y2 ≠ 0) ∨ y3 / 4096 % 2 = 1)

theorem fr_toNat (y3 : Nat) (h : y3 < 2 ^ 64) : (fr y3).toNat = y3 / 4096 := rot12 y3 h

theorem leaf0 (V bl y0 y1 y2 y3 : Nat) (e : BitVec 64) (he : e.toNat = bl) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V)
    (hbl : Spec.bitLen V = bl) (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256)
    (hn : ¬ Up y0 y1 y2 y3) : Form (fr y3) e = Fv256.B.float64BitsNearest V := by
  have hbl' : bl ≤ 256 := by
    have := (Util.bitLen_bounds V (by omega)).1; rw [hbl] at this
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 256 ≤ 2 ^ (bl - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  rw [f64_nearest V bl y0 y1 y2 y3 hV hge hbl h0 h1 h2 h3 hy]
  unfold Form
  rw [form_val _ e (by rw [fr_toNat _ h3]; omega) (by omega), fr_toNat _ h3]
  simp only [if_neg hn, he]

theorem leaf1 (V bl y0 y1 y2 y3 : Nat) (e : BitVec 64) (he : e.toNat = bl) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V)
    (hbl : Spec.bitLen V = bl) (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256)
    (hu : Up y0 y1 y2 y3) : Form (fr y3 + 1#64) e = Fv256.B.float64BitsNearest V := by
  have hbl' : bl ≤ 256 := by
    have := (Util.bitLen_bounds V (by omega)).1; rw [hbl] at this
    refine Classical.byContradiction fun hc => ?_
    have : 2 ^ 256 ≤ 2 ^ (bl - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hf := fr_toNat _ h3
  have hlt : y3 / 4096 < 2 ^ 52 := by omega
  have hadd : (fr y3 + 1#64).toNat = y3 / 4096 + 1 := by
    rw [BitVec.toNat_add, hf]; simp; omega
  rw [f64_nearest V bl y0 y1 y2 y3 hV hge hbl h0 h1 h2 h3 hy]
  unfold Form
  rw [form_val _ e (by rw [hadd]; omega) (by omega), hadd]
  simp only [if_pos hu, he]

theorem lsb_ofNat (y i : Nat) (hi : i < 64) : (BitVec.ofNat 64 y).getLsbD i = decide (y / 2 ^ i % 2 = 1) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  simp [hi]

theorem lsb0_toNat (v : BitVec 64) : v.getLsbD 0 = decide (v.toNat % 2 = 1) := by
  unfold BitVec.getLsbD
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp

/-- sticky-bit materialisation `if a|b|c = 0 then 0 else 1` seen through `getLsbD 0` -/
theorem ite_or_lsb (a b c : Nat) :
    (((if a ||| b ||| c = 0 then 0#64 else 1#64).getLsbD 0 == true) = true) ↔ (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) := by
  have hor : a ||| b ||| c = 0 ↔ (a = 0 ∧ b = 0 ∧ c = 0) := by
    simp only [Nat.or_eq_zero_iff, and_assoc]
  by_cases h : a ||| b ||| c = 0
  · have h' := hor.mp h
    rw [if_pos h]
    constructor
    · intro hh; simp at hh
    · rintro (h1 | h1 | h1) <;> exact absurd (by first | exact h'.1 | exact h'.2.1 | exact h'.2.2) h1
  · rw [if_neg h]
    constructor
    · intro _
      exact Classical.byContradiction fun hc => h (hor.mpr (by simp only [not_or, ne_eq, Decidable.not_not] at hc; exact hc))
    · intro _; decide

/-- the 0/1 sticky flag seen through `toNat % 2` (after `lsb0_toNat`) -/
theorem ite_toNat_mod2 (c : Prop) [Decidable c] : ((if c then 0#64 else 1#64).toNat % 2 = 1) ↔ ¬ c := by
  by_cases h : c <;> simp [h]

theorem pureForm (g a : Nat) (hg : g < 2 ^ 64) :
    ((a * 2 ^ 52 % 2 ^ 64) ||| g) % 340282366920938463463374607431768211456 =
      (g ||| 4503599627370496 * a % 18446744073709551616) % 18446744073709551616 % 340282366920938463463374607431768211456 % 18446744073709551616 := by
  have ht : ((a * 2 ^ 52 % 2 ^ 64) ||| g) < 2 ^ 64 := Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) hg
  rw [Nat.or_comm g, Nat.mul_comm 4503599627370496 a, show (4503599627370496 : Nat) = 2 ^ 52 by decide]
  generalize ((a * 2 ^ 52 % 2 ^ 64) ||| g) = t at *
  simp only [Nat.reducePow] at ht ⊢
  have h1 : t % 340282366920938463463374607431768211456 = t := Nat.mod_eq_of_lt (by omega)
  have h2 : t % 18446744073709551616 = t := Nat.mod_eq_of_lt ht
  rw [h1, h2, h1, h2]

/-- amd64 packing (`SHLQ`/`ORQ` form) equals the shared `Form` -/
theorem amd_eq_Form (G e : BitVec 64) :
    ((if (G >>> 52).toNat = 0 then e + 1022#64 else e + 1023#64) <<< 52 |||
        (if (G >>> 52).toNat = 0 then G else 0#64)).toNat % 340282366920938463463374607431768211456 = Form G e := by
  have hc : ((G >>> 52).toNat = 0) ↔ ((G.rotateRight 52).toNat % 4096 = 0) := by
    rw [rot52, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold Form
  by_cases h : (G >>> 52).toNat = 0
  · have h' := hc.mp h
    simp only [h, h', if_true]
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    exact pureForm _ _ G.isLt
  · have h' : ¬ ((G.rotateRight 52).toNat % 4096 = 0) := fun hh => h (hc.mpr hh)
    simp only [h, h', ite_false]
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    have := pureForm 0 (e + 1023#64).toNat (by decide)
    simpa using this

theorem shr12_eq_fr (y : Nat) (hy : y < 2 ^ 64) : BitVec.ofNat 64 y >>> 12 = fr y :=
  BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy, Nat.shiftRight_eq_div_pow, fr_toNat _ hy])

theorem shr64_zero (y : Nat) (hy : y < 2 ^ 64) : (BitVec.ofNat 64 y >>> 64).toNat = 0 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt hy

theorem shr12_lt (y : Nat) (hy : y < 2 ^ 64) : (BitVec.ofNat 64 y >>> 12 >>> 52).toNat = 0 := by
  rw [shr12_eq_fr y hy, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, fr_toNat _ hy]
  apply Nat.div_eq_of_lt; omega

theorem leafA0 (V bl y0 y1 y2 y3 : Nat) (e : BitVec 64) (he : e.toNat = bl) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V)
    (hbl : Spec.bitLen V = bl) (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256)
    (hn : ¬ Up y0 y1 y2 y3) :
    ((if (BitVec.ofNat 64 y3 >>> 64).toNat = 0 then e + 1022#64 else e + 1023#64) <<< 52 |||
        (if (BitVec.ofNat 64 y3 >>> 64).toNat = 0 then BitVec.ofNat 64 y3 >>> 12 else 0#64)).toNat %
      340282366920938463463374607431768211456 = Fv256.B.float64BitsNearest V := by
  rw [← leaf0 V bl y0 y1 y2 y3 e he hV hge hbl h0 h1 h2 h3 hy hn, ← shr12_eq_fr y3 h3, ← amd_eq_Form]
  simp only [shr64_zero y3 h3, shr12_lt y3 h3]

theorem leafA1 (V bl y0 y1 y2 y3 : Nat) (e : BitVec 64) (he : e.toNat = bl) (hV : V < 2 ^ 256) (hge : 2 ^ 64 ≤ V)
    (hbl : Spec.bitLen V = bl) (h0 : y0 < 2 ^ 64) (h1 : y1 < 2 ^ 64) (h2 : y2 < 2 ^ 64) (h3 : y3 < 2 ^ 64)
    (hy : y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3 = V * 2 ^ (257 - bl) % 2 ^ 256)
    (hu : Up y0 y1 y2 y3) :
    ((if ((BitVec.ofNat 64 y3 >>> 12 + 1#64) >>> 52).toNat = 0 then e + 1022#64 else e + 1023#64) <<< 52 |||
        (if ((BitVec.ofNat 64 y3 >>> 12 + 1#64) >>> 52).toNat = 0 then BitVec.ofNat 64 y3 >>> 12 + 1#64 else 0#64)).toNat %
      340282366920938463463374607431768211456 = Fv256.B.float64BitsNearest V := by
  rw [← leaf1 V bl y0 y1 y2 y3 e he hV hge hbl h0 h1 h2 h3 hy hu, shr12_eq_fr y3 h3, amd_eq_Form]

/-- amd64: bit `i < 32` of the 32-bit view of a 64-bit value -/
theorem lsb32 (y i : Nat) (hi : i < 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 y)).getLsbD i = decide (y / 2 ^ i % 2 = 1) := by
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  simp [hi, show i < 64 by omega]

/-- amd64: the sticky flag `(a | b | c) != 0` as materialised by the code -/
theorem sticky_iff (a b c : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    ((if (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b ||| BitVec.ofNat 64 c).toNat = 0 then true else false) = false) ↔
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) := by
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  by_cases h : (a ||| b ||| c) = 0
  · have := Nat.or_eq_zero_iff.mp h
    have := Nat.or_eq_zero_iff.mp this.1
    simp [h]; omega
  · have : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
      by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hc0 : c = 0 <;> simp_all
    simp [h, this]

theorem ite_tf (P : Prop) [Decidable P] : (if P then true else false) = decide P := by
  by_cases h : P <;> simp [h]

end Fv256.D
