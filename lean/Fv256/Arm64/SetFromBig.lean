import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC

/-!
# `(*uint256.Int).SetFromBig(b *big.Int) bool` (arm64)

`big.Int` is `{neg bool; abs nat}` with `nat = []Word`: `neg` at offset 0, the word array pointer at 8, its length at 16.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetFromBig

theorem correctness (z b pw len : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, b]
      (fun s => Ptr32 s.mem z true ∧ Ptr s.mem b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
        s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = len.toNat ∧
        Ptr s.mem pw (8 * len.toNat) false ∧
        Disjoint z.toNat 32 b.toNat 32 ∧ Disjoint z.toNat 32 pw.toNat (8 * len.toNat))
      (fun s s' => (s'.regs 0).toNat = (if Fv256.C.fromBigOv len.toNat then 1 else 0) ∧
        val256 s'.mem z.toNat =
          Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) len.toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32) := by
  intro ret hret s hs ⟨⟨hz, hz'⟩, ⟨hb, hb'⟩, hneg, hpw, hlen, ⟨hw, hw'⟩, hd1, hd2⟩
  janus_intro hs
  simp only [Disjoint] at hd1 hd2
  janus_run
  all_goals (
    simp only [hlen, hpw] at *
    have hl64 := len.isLt
    have l0 := Util.readLE8_lt s.mem pw.toNat
    have l1 := Util.readLE8_lt s.mem (pw.toNat + 8)
    have l2 := Util.readLE8_lt s.mem (pw.toNat + 16)
    have l3 := Util.readLE8_lt s.mem (pw.toNat + 24)
    have hn : s.mem.readLE b.toNat 1 = 0 ∨ s.mem.readLE b.toNat 1 = 1 := by omega
    have hc : len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ 5 ≤ len.toNat := by omega
    have e0 : (addWithCarry (0#64) (1#64) false).snd.z = false := by decide
    have e1 : (addWithCarry (18446744073709551615#64) (1#64) false).snd.z = true := by decide
    have e2 : (addWithCarry (1#64) (1#64) false).snd.z = false := by decide
    simp only [e0, e1, e2] at *
    rcases hn with hn | hn <;> rcases hc with h | h | h | h | h | h
    all_goals first
      | (exfalso; omega)
      | (exfalso; simp at hbr; done)
      | (simp only [Fv256.C.fromBig, Fv256.C.fromBigOv, Spec.neg, Spec.W]
         first
           | (rw [Fv256.C.bigAbs_mod _ _ (by omega : 4 ≤ len.toNat)]; simp only [h, hn, Fv256.C.bigAbs]; try simp)
           | (simp only [h, hn, Fv256.C.bigAbs]; try simp)))
  all_goals (try simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Spec.neg, Spec.W])
  all_goals (try simp only [Nat.cast_ofNat, Int.reduceLE, ↓reduceIte, decide_eq_true_eq, Nat.reduceLT, decide_false, Bool.false_eq_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Fv256.C.fromBigOv])
  all_goals (try (first | refine ⟨Fv256.C.ov_flag _, ?_⟩ | refine ⟨Fv256.C.ov_flag' _, ?_⟩))
  all_goals ((try generalize s.mem.readLE pw.toNat 8 = x0 at *); (try generalize s.mem.readLE (pw.toNat + 8) 8 = x1 at *); (try generalize s.mem.readLE (pw.toNat + 16) 8 = x2 at *); (try generalize s.mem.readLE (pw.toNat + 24) 8 = x3 at *); first | (janus_decide_split <;> omega) | omega | (trace_state; fail "y"))
  all_goals fail "x"

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def b : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigBase
def pw : BitVec 64 := BitVec.ofNat 64 Fv256.C.bigWords

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then b
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Fv256.C.bigMem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z true ∧ Ptr s0.mem b 32 false ∧ s0.mem.readLE b.toNat 1 < 2 ∧
    s0.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s0.mem.readLE (b.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
    Ptr s0.mem pw (8 * (2 : BitVec 64).toNat) false ∧
    Disjoint z.toNat 32 b.toNat 32 ∧ Disjoint z.toNat 32 pw.toNat (8 * (2 : BitVec 64).toNat) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide, by decide,
    ⟨by decide, by decide⟩, ?_, ?_⟩ <;> (unfold Disjoint; decide)

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z b pw : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, b] s ∧
    (Ptr32 s.mem z true ∧ Ptr s.mem b 32 false ∧ s.mem.readLE b.toNat 1 < 2 ∧
      s.mem.readLE (b.toNat + 8) 8 = pw.toNat ∧ s.mem.readLE (b.toNat + 16) 8 = (2 : BitVec 64).toNat ∧
      Ptr s.mem pw (8 * (2 : BitVec 64).toNat) false ∧
      Disjoint z.toNat 32 b.toNat 32 ∧ Disjoint z.toNat 32 pw.toNat (8 * (2 : BitVec 64).toNat)) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ (s'.regs 0).toNat = (if Fv256.C.fromBigOv (2 : BitVec 64).toNat then 1 else 0) ∧
        val256 s'.mem z.toNat =
          Fv256.C.fromBig (s.mem.readLE b.toNat 1 == 1)
            (Fv256.C.bigAbs (fun i => s.mem.readLE (pw.toNat + 8 * i) 8) (2 : BitVec 64).toNat) ∧
        OnlyWrites s.mem s'.mem z.toNat 32 :=
  ⟨ret, s0, z, b, pw, hret, setup, hpre,
    correctness z b pw (2 : BitVec 64) ret hret s0 setup hpre⟩


/-- The call returns, without overflow, and `z` holds `-(5 + 2^64)` modulo `2^256`. -/
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 0 ∧
      val256 s'.mem z.toNat = 2 ^ 256 - (5 + 2 ^ 64) := by
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

end Fv256.Arm64.SetFromBig
