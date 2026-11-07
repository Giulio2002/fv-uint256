import Fv256.Amd64.R4Seg0
import Fv256.Amd64.R4Live

/-! `reduce4` (amd64): the final `while r >= m { r -= m }` loop and the epilogue. -/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec

namespace Fv256.Amd64.R4Seg

theorem dt (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by by_cases h : p <;> simp [h]

theorem sub5_lt (c0 c1 c2 c3 c4 n0 n1 n2 n3 : Nat) (h0 : c0 < 2 ^ 64) (h1 : c1 < 2 ^ 64) (h2 : c2 < 2 ^ 64) (h3 : c3 < 2 ^ 64)
    (g0 : n0 < 2 ^ 64) (g1 : n1 < 2 ^ 64) (g2 : n2 < 2 ^ 64) (g3 : n3 < 2 ^ 64) :
    (c4 < (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat) ↔
    c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 < n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3 := by
  simp only [dt]
  iterate 6 (all_goals (try split))
  all_goals omega

/-- one subtraction step on five limbs (`R - M`, no final borrow): the new limbs -/
theorem sub5_val (c0 c1 c2 c3 c4 n0 n1 n2 n3 : Nat) (h0 : c0 < 2 ^ 64) (h1 : c1 < 2 ^ 64) (h2 : c2 < 2 ^ 64) (h3 : c3 < 2 ^ 64)
    (h4 : c4 < 2 ^ 64) (g0 : n0 < 2 ^ 64) (g1 : n1 < 2 ^ 64) (g2 : n2 < 2 ^ 64) (g3 : n3 < 2 ^ 64)
    (hge : n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3 ≤ c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) :
    (c0 + 2 ^ 64 - n0) % 2 ^ 64 + 2 ^ 64 * ((c1 + 2 ^ 64 - n1 - (decide (c0 < n0)).toNat) % 2 ^ 64) +
      2 ^ 128 * ((c2 + 2 ^ 64 - n2 - (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat) % 2 ^ 64) +
      2 ^ 192 * ((c3 + 2 ^ 64 - n3 - (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat) % 2 ^ 64) +
      2 ^ 256 * ((c4 + 2 ^ 64 - (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat) % 2 ^ 64) +
      (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) =
    c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 := by
  simp only [dt]
  iterate 6 (all_goals (try split))
  all_goals omega

/-- the five limbs of `r` (`RCX RDX RBX RSI R8`) and the four of `m` (`R9 R10 R12 RDI`) at the loop head, `z` saved at `sp+8` -/
def TInv (s S : State) (c0 c1 c2 c3 c4 n0 n1 n2 n3 zz : Nat) : Prop :=
  S.rip = BitVec.ofNat 64 (r4Entry + 0x4da) ∧
  S.regs 1 = BitVec.ofNat 64 c0 ∧ S.regs 2 = BitVec.ofNat 64 c1 ∧ S.regs 3 = BitVec.ofNat 64 c2 ∧
  S.regs 6 = BitVec.ofNat 64 c3 ∧ S.regs 8 = BitVec.ofNat 64 c4 ∧
  S.regs 9 = BitVec.ofNat 64 n0 ∧ S.regs 10 = BitVec.ofNat 64 n1 ∧ S.regs 12 = BitVec.ofNat 64 n2 ∧ S.regs 7 = BitVec.ofNat 64 n3 ∧
  c0 < 2 ^ 64 ∧ c1 < 2 ^ 64 ∧ c2 < 2 ^ 64 ∧ c3 < 2 ^ 64 ∧ c4 < 2 ^ 64 ∧
  n0 < 2 ^ 64 ∧ n1 < 2 ^ 64 ∧ n2 < 2 ^ 64 ∧ n3 < 2 ^ 64 ∧
  S.mem.readLE ((s.regs 4).toNat + 8) 8 = zz ∧
  R4Regs s S ∧ R4Mem s S.mem

def TailPost (s S' : State) (v : Nat) : Prop :=
  S'.regs 0 = s.regs 0 ∧ S'.regs 4 = s.regs 4 + 8 ∧ S'.regs 5 = s.regs 5 ∧ S'.regs 14 = s.regs 14 ∧
  S'.xmm 15 = s.xmm 15 ∧ S'.df = s.df ∧ S'.mxcsr = s.mxcsr ∧
  S'.mem.readLE (s.regs 0).toNat 32 = v ∧
  MemFrame s.mem S'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x120, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x10)]

theorem sub64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 ((a + 2 ^ 64 - b) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem sf64 (a b : Nat) (c : Bool) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (subFlags (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) c).fst = BitVec.ofNat 64 ((a + 2 ^ 64 - b - c.toNat) % 2 ^ 64) := by
  rw [subFlags_fst_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem wr_ok (sp : Nat) (h : 296 ≤ sp) : sp - 288 ≤ sp - 232 ∧ sp - 232 + 8 ≤ sp - 8 ∧ sp - 0x120 ≤ sp - 232 := by omega

theorem zw (z k : Nat) (hk : k + 8 ≤ 32) : z ≤ z + k ∧ z + k + 8 ≤ z + 32 := by omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem tail4 (s : State) (hs : R4Pre s) :
    ∀ (q c0 c1 c2 c3 c4 n0 n1 n2 n3 : Nat) (S : State),
      (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) / (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) = q →
      0 < n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3 →
      TInv s S c0 c1 c2 c3 c4 n0 n1 n2 n3 (s.regs 0).toNat →
      ReachesRet Fv256.ReduceProg.program (retAddrOf s) S
        (fun S' => TailPost s S' ((c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) % (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3))) := by
  intro q
  induction q with
  | zero =>
    intro c0 c1 c2 c3 c4 n0 n1 n2 n3 S hq hM0 hI
    obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
    clear hmu hm3 hdx hdm hdu hdg
    unfold Apart at hdz
    obtain ⟨hpc, r1, r2, r3, r6, r8, r9, r10, r12, r7, b0, b1, b2, b3, b4, b5, b6, b7, b8, mz, hR, hM⟩ := hI
    obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
    have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
    have hrb := hM.2
    simp only [regSP] at hacc hlow hnw hsp
    have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
      rw [hfr.accessible]; exact hacc
    have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
      rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hRM : (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) < (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) :=
      (Nat.div_eq_zero_iff.mp hq).resolve_left (by omega)
    have hc4 : c4 = 0 := by omega
    janus64_run [r1, r2, r3, r6, r8, r9, r10, r12, r7, mz, hrb, hsp4, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3, Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b5, Nat.mod_eq_of_lt b6, Nat.mod_eq_of_lt b7, Nat.mod_eq_of_lt b8] until [0x4b5c9a]
    · exfalso
      have hnb : ¬ (c4 < (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat) := by
        intro hh; simp [hh] at hbr
      exact hnb ((sub5_lt c0 c1 c2 c3 c4 n0 n1 n2 n3 b0 b1 b2 b3 b5 b6 b7 b8).mpr hRM)
    · have h1 : MemFrame s.mem S.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 4).toNat - 0x120, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x10)] :=
        hfr.mono (by intro a n h; simp [Outside] at h ⊢; omega)
      unfold TailPost
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, hrb]
      · simp [setRegF, hr14]
      · simp [setRegF, hx15]
      · simp [setRegF, hrdf]
      · simp [setRegF, hrmx]
      · simp only [Util.readLE_32]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]
        rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b0 (by decide)), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b1 (by decide)), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b2 (by decide)), Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b3 (by decide))]
        rw [hc4, Nat.mod_eq_of_lt (by omega)]
        omega
      · exact MemFrame.writeLE (MemFrame.writeLE (MemFrame.writeLE (MemFrame.writeLE (MemFrame.writeLE h1 c0 (r := ((s.regs 4).toNat - 0x120, (s.regs 4).toNat)) (by simp) (wr_ok _ hsp).2.2 (by have := (wr_ok _ hsp).2.1; omega)) c3 (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32)) (by simp) (zw _ 24 (by decide)).1 (zw _ 24 (by decide)).2) c2 (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32)) (by simp) (zw _ 16 (by decide)).1 (zw _ 16 (by decide)).2) c1 (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32)) (by simp) (zw _ 8 (by decide)).1 (zw _ 8 (by decide)).2) c0 (r := ((s.regs 0).toNat, (s.regs 0).toNat + 32)) (by simp) (zw _ 0 (by decide)).1 (by have := (zw (s.regs 0).toNat 0 (by decide)).2; simpa using this)
  | succ q ih =>
    intro c0 c1 c2 c3 c4 n0 n1 n2 n3 S hq hM0 hI
    obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hs
    clear hmu hm3 hdx hdm hdu hdg
    unfold Apart at hdz
    obtain ⟨hpc, r1, r2, r3, r6, r8, r9, r10, r12, r7, b0, b1, b2, b3, b4, b5, b6, b7, b8, mz, hR, hM⟩ := hI
    obtain ⟨hr4, hr5, hr14, hx15, hrdf, hrmx⟩ := hR
    have hfr : MemFrame s.mem S.mem [((s.regs 4).toNat - 288, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 16)] := hM.1
    have hrb := hM.2
    simp only [regSP] at hacc hlow hnw hsp
    have hacc' : S.mem.accessible ((s.regs 4).toNat - 288) (288 + 16) true = true := by
      rw [hfr.accessible]; exact hacc
    have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 288 := by
      rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    janus64_run [r1, r2, r3, r6, r8, r9, r10, r12, r7, mz, hrb, hsp4, Nat.mod_eq_of_lt b0, Nat.mod_eq_of_lt b1, Nat.mod_eq_of_lt b2, Nat.mod_eq_of_lt b3, Nat.mod_eq_of_lt b4, Nat.mod_eq_of_lt b5, Nat.mod_eq_of_lt b6, Nat.mod_eq_of_lt b7, Nat.mod_eq_of_lt b8] until [0x4b5c9a]
    · have hnb : ¬ (c4 < (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat) := by
        intro hh; simp [hh] at hbr
      have hge : n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3 ≤ c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4 :=
        Nat.not_lt.mp (fun hh => hnb ((sub5_lt c0 c1 c2 c3 c4 n0 n1 n2 n3 b0 b1 b2 b3 b5 b6 b7 b8).mpr hh))
      have hval := sub5_val c0 c1 c2 c3 c4 n0 n1 n2 n3 b0 b1 b2 b3 b4 b5 b6 b7 b8 hge
      generalize hd0 : (c0 + 2 ^ 64 - n0) % 2 ^ 64 = d0 at hval
      generalize hd1 : (c1 + 2 ^ 64 - n1 - (decide (c0 < n0)).toNat) % 2 ^ 64 = d1 at hval
      generalize hd2 : (c2 + 2 ^ 64 - n2 - (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat) % 2 ^ 64 = d2 at hval
      generalize hd3 : (c3 + 2 ^ 64 - n3 - (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat) % 2 ^ 64 = d3 at hval
      generalize hd4 : (c4 + 2 ^ 64 - (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat) % 2 ^ 64 = d4 at hval
      have hq' : (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4) / (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) = q := by
        have h2 := Nat.add_div_right (x := d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4)
          (z := n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) hM0
        rw [hval] at h2
        omega
      have hd0' : d0 < 2 ^ 64 := hd0 ▸ Nat.mod_lt _ (by decide)
      have hd1' : d1 < 2 ^ 64 := hd1 ▸ Nat.mod_lt _ (by decide)
      have hd2' : d2 < 2 ^ 64 := hd2 ▸ Nat.mod_lt _ (by decide)
      have hd3' : d3 < 2 ^ 64 := hd3 ▸ Nat.mod_lt _ (by decide)
      have hd4' : d4 < 2 ^ 64 := hd4 ▸ Nat.mod_lt _ (by decide)
      have hmod : (d0 + 2 ^ 64 * d1 + 2 ^ 128 * d2 + 2 ^ 192 * d3 + 2 ^ 256 * d4) % (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) =
          (c0 + 2 ^ 64 * c1 + 2 ^ 128 * c2 + 2 ^ 192 * c3 + 2 ^ 256 * c4) % (n0 + 2 ^ 64 * n1 + 2 ^ 128 * n2 + 2 ^ 192 * n3) := by
        rw [← hval, Nat.add_mod_right]
      refine Fv256.SegCompose.seg_mono (ih d0 d1 d2 d3 d4 n0 n1 n2 n3 _ hq' hM0 ?_) (fun S' h => by rw [← hmod]; exact h)
      unfold TInv
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hd0', hd1', hd2', hd3', hd4', b5, b6, b7, b8, ?_, ?_, ?_⟩
      · first | rfl | decide | simp [r4Entry]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [sub64 _ _ b0 b5, hd0]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [sf64 _ _ _ b1 b6, hd1]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [sf64 _ _ _ b2 b7, hd2]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]; rw [sf64 _ _ _ b3 b8, hd3]
      · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]
        rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sf64 _ _ _ b4 (by decide), ← hd4]
        simp
      · simp [setRegF, r9]
      · simp [setRegF, r10]
      · simp [setRegF, r12]
      · simp [setRegF, r7]
      · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]; exact mz
      · unfold R4Regs
        and_intros <;> first | rfl | simp [setRegF, hr4, hr5, hr14, hx15, hrdf, hrmx]
      · exact R4Mem.write hM _ _ _ (wr_ok _ hsp).1 (wr_ok _ hsp).2.1
    · exfalso
      have hb : ¬ (if c4 < (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat then 1#64 else 0#64).toNat = 0 := by assumption
      rcases Nat.lt_or_ge c4 (decide (c3 < n3 + (decide (c2 < n2 + (decide (c1 < n1 + (decide (c0 < n0)).toNat)).toNat)).toNat)).toNat with hlt | hge
      · have hRM := (sub5_lt c0 c1 c2 c3 c4 n0 n1 n2 n3 b0 b1 b2 b3 b5 b6 b7 b8).mp hlt
        have := Nat.div_eq_of_lt hRM
        omega
      · exact hb (by simp [Nat.not_lt.mpr hge])

end Fv256.Amd64.R4Seg
