import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.SpecC
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.UtilC
import Fv256.Proofs.Common.SumC64
import Fv256.Proofs.Amd64.CmpBigSfb
import Fv256.Proofs.Amd64.CmpBigCmp

/-!
# `(*uint256.Int).CmpBig(x *big.Int) int` (amd64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word` (normalised: no leading zero word, as `math/big` maintains).
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Tactic

namespace Fv256.Amd64.CmpBig

set_option maxHeartbeats 16000000 in
theorem correctness (z x pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, x]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 72 16 ∧ Buffer s z 32 false ∧ Buffer s x 32 false ∧
        s.mem.readLE x.toNat 1 < 2 ∧
        s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = len.toNat ∧
        Buffer s pw (8 * len.toNat) false ∧
        (len.toNat = 0 ∨ s.mem.readLE (pw.toNat + 8 * (len.toNat - 1)) 8 ≠ 0) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
        (x.toNat + 32 ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
        (pw.toNat + 8 * len.toNat ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ pw.toNat))
      (fun s s' => s'.regs 0 = BitVec.ofInt 64
          (Fv256.C.cmpBig (valueAt s z 32)
            (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat))) ∧
        Janus.MemFrame s.mem s'.mem [((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 16),
          ((s.regs regSP).toNat - 72, (s.regs regSP).toNat)]) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hneg, hpw, hlen, ⟨hw1', hw1⟩, hnorm, hd1, hd2, hd3⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd1 hd2 hd3
  simp only [valueAt]
  have hwlt : ∀ i, s.mem.readLE (pw.toNat + 8 * i) 8 < 2 ^ 64 := fun i => Util.readLE8_lt _ _
  have hzlt : s.mem.readLE z.toNat 32 < 2 ^ 256 := by
    have h := Janus.Arm64.Memory.readLE_lt s.mem z.toNat 32
    simpa [Nat.reducePow] using h
  have hx1 : s.mem.readLE x.toNat 1 = 0 ∨ s.mem.readLE x.toNat 1 = 1 := by omega
  have hpos : 0 < len.toNat → 0 < Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat := fun h =>
    Fv256.C.bigAbs_pos _ _ h (by rcases hnorm with h' | h' <;> first | omega | exact h')
  have hbig : 4 < len.toNat → 2 ^ 256 ≤ Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat := fun h =>
    Fv256.C.bigAbs_big _ _ h (by rcases hnorm with h' | h' <;> first | omega | exact h')
  have hsmall : len.toNat ≤ 4 → Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat < 2 ^ 256 := fun h =>
    Fv256.C.bigAbs_small _ hwlt _ h
  have h0 : len.toNat = 0 → Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat = 0 := fun h => by
    rw [h]; rfl
  janus64_run calls [Fv256.Amd64.CmpBigSfb.sfb_summary (s.regs 4 - 40#64) x pw len,
    Fv256.Amd64.CmpBigCmp.cmp_summary z (s.regs 4 - 40#64)]
  · refine And.intro ?_ ?_
    · rename_i hl s1 a1 g0 g1 g2 g3 g4 g5 g6 hflag hval hfr a2 c0 c1 c2 c3 c4 c5 c6 c7 cm
      have hnov := Fv256.C.noov_of64 _ _ hflag hbr
      have hl4 := Fv256.C.ovF _ hnov
      have hd3' := hd3
      rw [hl] at hd3'
      rw [Util.readLE_32 _ (BitVec.toNat (s.regs 4) - 40), hval]
      rw [Fv256.C.bigAbs_stackframe64 s.mem _ _ _ _ _ _ pw.toNat _ (Nat.le_trans (by decide) hlow) hd3']
      rw [hl] at hsmall h0
      exact congrArg (BitVec.ofInt 64) (Fv256.C.cmpBig_core _ _ 0 _ hzlt
        (fun ⟨_, h⟩ => absurd rfl h) hl4 (hsmall hl4) h0)
    · janus_frame
  · refine And.intro ?_ ?_
    · rename_i hl a g0 g1 g2 g3 g4 g5 g6 hflag hval hfr
      have hov' := Fv256.C.ov_of64 _ _ hflag hbr
      have h4 := Fv256.C.ovT _ hov'
      exact absurd h4 (by decide)
    · janus_frame
  · refine And.intro ?_ ?_
    · rename_i hl hbit s1 a1 g0 g1 g2 g3 g4 g5 g6 hflag hval hfr a2 c0 c1 c2 c3 c4 c5 c6 c7 cm
      have hnov := Fv256.C.noov_of64 _ _ hflag hbr
      have hl4 := Fv256.C.ovF _ hnov
      have hb0 := Fv256.C.bit0_8 _ hneg hbit
      rw [Util.readLE_32 _ (BitVec.toNat (s.regs 4) - 40), hval]
      rw [Fv256.C.bigAbs_stackframe64 s.mem _ _ _ _ _ _ pw.toNat _ (Nat.le_trans (by decide) hlow) hd3]
      exact congrArg (BitVec.ofInt 64) (Fv256.C.cmpBig_core _ _ len.toNat _ hzlt
        (fun ⟨h, _⟩ => by rw [hb0] at h; exact Bool.noConfusion h) hl4 (hsmall hl4) h0)
    · janus_frame
  · refine And.intro ?_ ?_
    · rename_i hl hbit a g0 g1 g2 g3 g4 g5 g6 hflag hval hfr
      have hov' := Fv256.C.ov_of64 _ _ hflag hbr
      have h4 := Fv256.C.ovT _ hov'
      have hb0 := Fv256.C.bit0_8 _ hneg hbit
      rw [hb0, Fv256.C.cmpBig_big _ _ (Nat.lt_of_lt_of_le hzlt (hbig h4))]
      decide
    · janus_frame
  · refine And.intro ?_ ?_
    · rename_i hlne
      have hb1 := Fv256.C.bit1_8 _ hneg hbr
      have hl : 0 < len.toNat := Nat.pos_of_ne_zero hlne
      rw [hb1, Fv256.C.cmpBig_neg _ _ (hpos hl)]
      rfl
    · janus_frame

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def x : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then x else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := Fv256.C.bigMem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 72 16 ∧ Buffer s0 z 32 false ∧ Buffer s0 x 32 false ∧
    s0.mem.readLE x.toNat 1 < 2 ∧
    s0.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (x.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
    Buffer s0 pw (8 * (2 : BitVec 64).toNat) false ∧
    ((2 : BitVec 64).toNat = 0 ∨ s0.mem.readLE (pw.toNat + 8 * ((2 : BitVec 64).toNat - 1)) 8 ≠ 0) ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 72 ∨ (s0.regs regSP).toNat + 16 ≤ z.toNat) ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 72 ∨ (s0.regs regSP).toNat + 16 ≤ x.toNat) ∧
    (pw.toNat + 8 * (2 : BitVec 64).toNat ≤ (s0.regs regSP).toNat - 72 ∨ (s0.regs regSP).toNat + 16 ≤ pw.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
   ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide, by decide,
   ⟨by decide, by decide⟩, Or.inr (by decide), by decide, by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z x pw : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, x] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 72 16 ∧ Buffer s z 32 false ∧ Buffer s x 32 false ∧
      s.mem.readLE x.toNat 1 < 2 ∧
      s.mem.readLE (x.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (x.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Buffer s pw (8 * (2 : BitVec 64).toNat) false ∧
      ((2 : BitVec 64).toNat = 0 ∨ s.mem.readLE (pw.toNat + 8 * ((2 : BitVec 64).toNat - 1)) 8 ≠ 0) ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ z.toNat) ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ x.toNat) ∧
      (pw.toNat + 8 * (2 : BitVec 64).toNat ≤ (s.regs regSP).toNat - 72 ∨ (s.regs regSP).toNat + 16 ≤ pw.toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ s'.regs 0 = BitVec.ofInt 64
          (Fv256.C.cmpBig (valueAt s z 32)
            (Fv256.C.bigVal (s.mem.readLE x.toNat 1 == 1)
              (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) (2 : BitVec 64).toNat))) ∧
        Janus.MemFrame s.mem s'.mem [((s.regs regSP).toNat + 8, (s.regs regSP).toNat + 16),
          ((s.regs regSP).toNat - 72, (s.regs regSP).toNat)] :=
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
  have hz : valueAt s0 z 32 = 0 := by decide
  rw [hz, Fv256.C.cmpBig_neg _ _ (by omega)]
  decide

end Witness

end Fv256.Amd64.CmpBig
