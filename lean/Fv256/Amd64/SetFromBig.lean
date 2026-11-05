import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).SetFromBig(b *big.Int) bool` (amd64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word`: `neg` at offset 0, the word array pointer at 8, its length at 16.
The Go ABI returns the bool in `AL` only, so the statement is about the low byte of `RAX`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetFromBig

set_option maxHeartbeats 8000000 in
theorem correctness (z b pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b]
      (fun s => StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
        s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
        Buffer s pw (8 * len.toNat) false ∧
        Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * len.toNat) ∧ Disjoint z 32 (s.regs regSP) 8)
      (fun s s' => (s'.regs 0).toNat % 256 = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
        valueAt s' z 32 =
          Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
        Janus.Spec.OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hz', hz⟩, ⟨hb', hb⟩, hneg, hpw, hlen, ⟨hw', hw⟩, hd1, hd2, hds⟩
  janus64_intro hs
  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw hds
  simp only [valueAt, Disjoint] at *
  janus64_run [Util.readLE_32]
  all_goals
    refine And.intro ?_ (And.intro ?_ ?_)
    · first | exact Fv256.C.ov8 _ | (rw [show (Fv256.C.fromBigOv 0).toNat = 0 from rfl]; exact Fv256.C.lowbyte0 z)
    · simp only [hlen, hpw] at *
      have hl64 := len.isLt
      have l0 := Util.readLE8_lt s.mem pw.toNat
      have l1 := Util.readLE8_lt s.mem (pw.toNat + 8)
      have l2 := Util.readLE8_lt s.mem (pw.toNat + 16)
      have l3 := Util.readLE8_lt s.mem (pw.toNat + 24)
      have hn : s.mem.readLE b.toNat 1 = 0 ∨ s.mem.readLE b.toNat 1 = 1 := by omega
      have hc : len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ 5 ≤ len.toNat := by omega
      rcases hn with hn | hn <;> rcases hc with h | h | h | h | h | h
      all_goals first
        | (exfalso; omega)
        | (exfalso; simp at hbr; done)
        | (exfalso; simp [hn] at hbr; done)
        | (simp only [Fv256.C.fromBig, Fv256.C.fromBigOv, Spec.neg, Spec.W]
           first
             | (rw [Fv256.C.bigAbs_mod _ _ (by omega : 4 ≤ len.toNat)]; simp only [h, hn, Fv256.C.bigAbs]; try simp)
             | (simp only [h, hn, Fv256.C.bigAbs]; try simp))
      all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Spec.neg, Spec.W])
      all_goals (try simp only [Nat.cast_ofNat, Int.reduceLE, ↓reduceIte, decide_eq_true_eq, Nat.reduceLT, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fv256.C.fromBigOv])
      all_goals ((try generalize s.mem.readLE pw.toNat 8 = x0 at *); (try generalize s.mem.readLE (pw.toNat + 8) 8 = x1 at *); (try generalize s.mem.readLE (pw.toNat + 16) 8 = x2 at *); (try generalize s.mem.readLE (pw.toNat + 24) 8 = x3 at *); first | (have key := Util.neg_chain x0 x1 x2 x3 l0 l1 l2 l3; have e : (x0 + x1 * 18446744073709551616 + x2 * 340282366920938463463374607431768211456 + x3 * 6277101735386680763835789423207666416102355444464034512896) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = (x0 + x1 * 18446744073709551616 + x2 * 340282366920938463463374607431768211456 + x3 * 6277101735386680763835789423207666416102355444464034512896) := Nat.mod_eq_of_lt (by omega); rw [e]; omega) | (have key := Util.neg_chain x0 0 0 0 l0 (by decide) (by decide) (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 0 0 l0 l1 (by decide) (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 x2 0 l0 l1 l2 (by decide); simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (have key := Util.neg_chain x0 x1 x2 x3 l0 l1 l2 l3; simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at key; omega) | (janus_decide_split <;> omega) | omega | (trace_state; fail "y"))
    · repeat (refine (Janus.Spec.onlyWrites_writeLE_iff _ (by omega) (by omega)).2 ?_)
      exact Janus.Spec.onlyWrites_refl _ _ _

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def b : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then b else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := Fv256.C.bigMem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 b 32 false ∧ s0.mem.readLE b.toNat 1 < 2 ∧
    s0.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (b.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
    Buffer s0 pw (8 * (2 : BitVec 64).toNat) false ∧
    Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * (2 : BitVec 64).toNat) ∧ Disjoint z 32 (s0.regs regSP) 8 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide, by decide,
    ⟨by decide, by decide⟩, by unfold Disjoint; decide, by unfold Disjoint; decide, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b pw : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b] s ∧
    (StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
      s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Buffer s pw (8 * (2 : BitVec 64).toNat) false ∧
      Disjoint z 32 b 32 ∧ Disjoint z 32 pw (8 * (2 : BitVec 64).toNat) ∧ Disjoint z 32 (s.regs regSP) 8) :=
  ⟨ret, s0, z, b, pw, hret, setup, hpre⟩

/-- The call returns, without overflow (low byte of `RAX` is 0), and `z` holds `-(5 + 2^64)` modulo `2^256`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat % 256 = 0 ∧
      valueAt s' z 32 = 2 ^ 256 - (5 + 2 ^ 64) := by
  refine (correctness z b pw 2 ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_, ?_⟩
  · rw [h.2.1]; decide
  · rw [h.2.2.1]
    have : Fv256.C.bigAbs (fun i => s0.mem.readLE (pw.toNat + 8 * i) 8) (2 : BitVec 64).toNat = 5 + 2 ^ 64 := by
      show Fv256.C.bigAbs (fun i => s0.mem.readLE (pw.toNat + 8 * i) 8) 2 = _
      simp only [Fv256.C.bigAbs]
      decide
    rw [this]
    have hn : (s0.mem.readLE b.toNat 1 == 1) = true := by decide
    rw [hn]
    simp only [Fv256.C.fromBig, Spec.neg, Spec.W]
    decide

end Witness

end Fv256.Amd64.SetFromBig
