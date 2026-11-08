import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC
import Fv256.Arm64.CmpBigSfb
import Fv256.Arm64.CmpBigCmp

/-!
# `(*uint256.Int).CmpBig(x *big.Int) int` (arm64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word` (normalised: no leading zero word, as `math/big` maintains).
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.CmpBig

set_option maxHeartbeats 16000000 in
theorem correctness (z x pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => GuardOK s 0 ∧ StackOK s 72 16 ∧ Ptr32 s.mem z false ∧ Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
        s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
        Ptr s.mem pw (8 * len.toNat) false ∧
        (len.toNat = 0 ∨ s.mem.readLE (pw.toNat + 8 * (len.toNat - 1)) 8 ≠ 0) ∧
        Disjoint z.toNat 32 (s.sp.toNat - 72) 88 ∧ Disjoint x.toNat 32 (s.sp.toNat - 72) 88 ∧
        Disjoint pw.toNat (8 * len.toNat) (s.sp.toNat - 72) 88 ∧ s.regs 29 = s.sp - 8#64)
      (fun s s' => s'.regs 0 = BitVec.ofInt 64
          (Fv256.C.cmpBig (val256 s.mem z.toNat)
            (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat))) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat - 72, s.sp.toNat)]) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hneg, hpw, hlen, ⟨hw1, hw1'⟩, hnorm, hd1, hd2, hd3, hfp⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2 hd3
  have hwlt : ∀ i, s.mem.readLE (pw.toNat + 8 * i) 8 < 2 ^ 64 := fun i => Util.readLE8_lt _ _
  have hzl0 := Util.readLE8_lt s.mem z.toNat
  have hzl1 := Util.readLE8_lt s.mem (z.toNat + 8)
  have hzl2 := Util.readLE8_lt s.mem (z.toNat + 16)
  have hzl3 := Util.readLE8_lt s.mem (z.toNat + 24)
  have hzlt : s.mem.readLE z.toNat 8 + 18446744073709551616 * s.mem.readLE (z.toNat + 8) 8 +
      340282366920938463463374607431768211456 * s.mem.readLE (z.toNat + 16) 8 +
      6277101735386680763835789423207666416102355444464034512896 * s.mem.readLE (z.toNat + 24) 8 <
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by omega
  have hx1 : s.mem.readLE x.toNat 1 = 0 ∨ s.mem.readLE x.toNat 1 = 1 := by omega
  have hpos : 0 < len.toNat → 0 < Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat := fun h =>
    Fv256.C.bigAbs_pos _ _ h (by rcases hnorm with h' | h' <;> first | omega | exact h')
  have hbig : 4 < len.toNat → 2 ^ 256 ≤ Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat := fun h =>
    Fv256.C.bigAbs_big _ _ h (by rcases hnorm with h' | h' <;> first | omega | exact h')
  have hsmall : len.toNat ≤ 4 → Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat < 2 ^ 256 := fun h =>
    Fv256.C.bigAbs_small _ hwlt _ h
  have h0 : len.toNat = 0 → Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat = 0 := fun h => by
    rw [h]; rfl
  have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
  janus_run calls [Fv256.Arm64.CmpBigSfb.sfb_summary pw len, Fv256.Arm64.CmpBigCmp.cmp_summary z (s.sp - 40#64)]
  all_goals first
    | (exfalso; revert hbr; decide)
    | (exfalso; exact absurd e1 ‹¬(addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true›)
    | (rename_i hq1 hq2
       have hb1 : s.mem.readLE x.toNat 1 = 1 := Fv256.C.bit1 _ hneg hq2
       have hl : 0 < len.toNat := by rw [← hlen]; exact Nat.pos_of_ne_zero hq1
       refine And.intro (Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb)) (And.intro ?_ ?_)
       · rw [hb1]; simp only [beq_self_eq_true]; rw [Fv256.C.cmpBig_neg _ _ (hpos hl)]; rfl
       · janus_frame)
    | (refine And.intro (Fv256.C.ofNat_sub8 _ (Nat.le_trans (by decide) hb)) (And.intro ?_ ?_)
       · first
         | (rename_i hl hcalc s1 a1 la lb lc ld le lf hflag hval hfr a2 m1 m2 m3 m4 m5 m6 m7 m8
            have hnov := Fv256.C.noov_of _ _ hflag hbr
            have hl4 := Fv256.C.ovF _ hnov
            have hl0 : len.toNat = 0 := by rw [← hlen]; exact hl
            rw [Fv256.C.bigAbs_stackframe s.mem _ _ z.toNat pw.toNat len.toNat (Nat.le_trans (by decide) hb)
              hd3] at hval
            rw [hval]
            exact congrArg (BitVec.ofInt 64) (Fv256.C.cmpBig_core _ _ len.toNat _ hzlt
              (fun ⟨_, h⟩ => absurd hl0 h) hl4 (hsmall hl4) h0))
         | (rename_i g hl hbit hcalc s1 a1 la lb lc ld le lf hflag hval hfr a2 m1 m2 m3 m4 m5 m6 m7 m8
            have hnov := Fv256.C.noov_of _ _ hflag hbr
            have hl4 := Fv256.C.ovF _ hnov
            have hb0 := Fv256.C.bit0 _ hneg hbit
            rw [Fv256.C.bigAbs_stackframe s.mem _ _ z.toNat pw.toNat len.toNat (Nat.le_trans (by decide) hb)
              hd3] at hval
            rw [hval]
            exact congrArg (BitVec.ofInt 64) (Fv256.C.cmpBig_core _ _ len.toNat _ hzlt
              (fun ⟨h, _⟩ => by rw [hb0] at h; exact Bool.noConfusion h) hl4 (hsmall hl4) h0))
         | (rename_i g hl hbit hcalc a l7 l6 l5 l4 l3 l2 hflag hval hfr
            have hov' := Fv256.C.ov_of _ _ hflag hbr
            have h4 := Fv256.C.ovT _ hov'
            have hb0 := Fv256.C.bit0 _ hneg hbit
            rw [hb0, Fv256.C.cmpBig_big _ _ (Nat.lt_of_lt_of_le hzlt (hbig h4))]
            decide)
         | (rename_i hl hcalc a l7 l6 l5 l4 l3 l2 hflag hval hfr
            have hov' := Fv256.C.ov_of _ _ hflag hbr
            have h4 := Fv256.C.ovT _ hov'
            have hl0 : len.toNat = 0 := by rw [← hlen]; exact hl
            exact absurd h4 (by rw [hl0]; decide))
       · janus_frame)

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then x
      else if i = 28 then BitVec.ofNat 64 wg else if i = 29 then BitVec.ofNat 64 wsp - 8#64
      else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Fv256.C.bigMem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 72 16 ∧ Ptr32 s0.mem z false ∧ Ptr s0.mem x 32 false ∧ s0.mem.readLE x.toNat 1 < 2 ∧
    s0.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (x.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
    Ptr s0.mem pw (8 * (2 : BitVec 64).toNat) false ∧
    ((2 : BitVec 64).toNat = 0 ∨ s0.mem.readLE (pw.toNat + 8 * ((2 : BitVec 64).toNat - 1)) 8 ≠ 0) ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 72) 88 ∧ Disjoint x.toNat 32 (s0.sp.toNat - 72) 88 ∧
    Disjoint pw.toNat (8 * (2 : BitVec 64).toNat) (s0.sp.toNat - 72) 88 ∧ s0.regs 29 = s0.sp - 8#64 := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide,
    by decide, by decide, ⟨by decide, by decide⟩, Or.inr (by decide), ?_, ?_, ?_, rfl⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x pw : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (GuardOK s 0 ∧ StackOK s 72 16 ∧ Ptr32 s.mem z false ∧ Ptr s.mem x 32 false ∧ s.mem.readLE x.toNat 1 < 2 ∧
      s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Ptr s.mem pw (8 * (2 : BitVec 64).toNat) false ∧
      ((2 : BitVec 64).toNat = 0 ∨ s.mem.readLE (pw.toNat + 8 * ((2 : BitVec 64).toNat - 1)) 8 ≠ 0) ∧
      Disjoint z.toNat 32 (s.sp.toNat - 72) 88 ∧ Disjoint x.toNat 32 (s.sp.toNat - 72) 88 ∧
      Disjoint pw.toNat (8 * (2 : BitVec 64).toNat) (s.sp.toNat - 72) 88 ∧ s.regs 29 = s.sp - 8#64) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = BitVec.ofInt 64
          (Fv256.C.cmpBig (val256 s.mem z.toNat)
            (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) (2 : BitVec 64).toNat))) ∧
        MemFrame s.mem s'.mem [(s.sp.toNat + 8, s.sp.toNat + 16), (s.sp.toNat - 72, s.sp.toNat)] :=
  ⟨ret, s0, z, x, pw, hret, setup, hpre,
    correctness z x pw (2 : BitVec 64) ret hret s0 setup hpre⟩


/-- `0` compared with `-(5 + 2^64)`: the result is `+1`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = 1 := by
  refine (correctness z x pw 2 ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2.1]
  have : Fv256.C.bigAbs (fun i => s0.mem.readLE (pw.toNat + 8 * i) 8) (2 : BitVec 64).toNat = 5 + 2 ^ 64 := by
    show Fv256.C.bigAbs (fun i => s0.mem.readLE (pw.toNat + 8 * i) 8) 2 = _
    simp only [Fv256.C.bigAbs]
    decide
  rw [this]
  have hn : (s0.mem.readLE x.toNat 1 == 1) = true := by decide
  rw [hn]
  have hz : val256 s0.mem z.toNat = 0 := by decide
  rw [hz, Fv256.C.cmpBig_neg _ _ (by omega)]
  decide

end Witness

end Fv256.Arm64.CmpBig
