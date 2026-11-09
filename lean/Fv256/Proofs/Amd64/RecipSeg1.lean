import Fv256.Proofs.Amd64.RecipSeg0

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

/-- `t1 = ⌊r0² · y3 / 2^64⌋` -/
def t1f (y3 : Nat) : Nat := r0f y3 * r0f y3 * y3 / 2 ^ 64
/-- `rax` after stage 1: `2 (r0 · 2^32 − t1)` -/
def r1rawf (y3 : Nat) : Nat := 2 * (r0f y3 * 2 ^ 32 - t1f y3)

theorem r0f_lt (y3 : Nat) (h1 : 2 ^ 63 ≤ y3) (h2 : y3 < 2 ^ 64) : r0f y3 < 2 ^ 32 := by
  unfold r0f
  split
  · decide
  · rename_i hne
    have hge : 2 ^ 31 ≤ y3 / 2 ^ 32 := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 32)).2 (by omega)
    have hlt : y3 / 2 ^ 32 < 2 ^ 32 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 32)).2 (by omega)
    have hgt : 2 ^ 31 < y3 / 2 ^ 32 := by omega
    have : 2 ^ 63 / (y3 / 2 ^ 32) ≤ 2 ^ 63 / (2 ^ 31 + 1) := Nat.div_le_div_left (by omega) (by omega)
    have h3 : 2 ^ 63 / (2 ^ 31 + 1) < 2 ^ 32 := by decide
    omega



set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem t1f_le (y3 : Nat) (h1 : 2 ^ 63 ≤ y3) (h2 : y3 < 2 ^ 64) : t1f y3 ≤ r0f y3 * 2 ^ 32 := by
  have hr := r0f_lt y3 h1 h2
  unfold t1f
  have : r0f y3 * r0f y3 * y3 / 2 ^ 64 ≤ r0f y3 * r0f y3 := by
    apply Nat.div_le_of_le_mul
    have : r0f y3 * r0f y3 * y3 ≤ r0f y3 * r0f y3 * 2 ^ 64 := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm (2 ^ 64)]
    exact this
  have h3 : r0f y3 * r0f y3 ≤ r0f y3 * 2 ^ 32 := Nat.mul_le_mul_left _ (by omega)
  omega

theorem rax_eq (y3 : Nat) (h1 : 2 ^ 63 ≤ y3) (h2 : y3 < 2 ^ 64) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (r0f y3))) <<< 32 -
        BitVec.ofNat 64
          ((BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (r0f y3))) *
                BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (r0f y3)))).toNat * y3 / 18446744073709551616)) =
      BitVec.ofNat 64 (r0f y3 * 2 ^ 32 - t1f y3) := by
  have hr := r0f_lt y3 h1 h2
  have hle := t1f_le y3 h1 h2
  have hsw : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (r0f y3))) = BitVec.ofNat 64 (r0f y3) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [hsw]
  apply BitVec.eq_of_toNat_eq
  have hmul : (BitVec.ofNat 64 (r0f y3) * BitVec.ofNat 64 (r0f y3)).toNat = r0f y3 * r0f y3 := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    have : r0f y3 * r0f y3 < 2 ^ 64 := by
      have := Nat.mul_lt_mul'' hr hr
      simpa [← Nat.pow_add] using this
    have h64 : r0f y3 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h64]
    exact Nat.mod_eq_of_lt this
  rw [hmul]
  have ht : r0f y3 * r0f y3 * y3 / 18446744073709551616 = t1f y3 := by unfold t1f; rfl
  rw [ht]
  simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have h4 : t1f y3 < 2 ^ 64 := by
    have : r0f y3 * 2 ^ 32 < 2 ^ 64 := by omega
    omega
  have h5 : r0f y3 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5]
  simp only [Nat.shiftLeft_eq]
  omega


theorem add_self_ofNat (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 x = BitVec.ofNat 64 (2 * x) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- the state at `recEntry + 0x14c`: `r1raw` in `RAX`, `y3 + y3` in `RBX`, their `or` in `RDX`, `bsr + 192` in `RCX`, `y2 y1 y0` in
`RDI R8 R9` and copied to the spill slots `sp-32 sp-40 sp-48`, `y3` at `sp-24` -/
def RecQ1 (s S' : State) : Prop := ∃ y3 y2 y1 y0 : Nat,
  S'.regs 6 = BitVec.ofNat 64 y3 ∧ S'.regs 0 = BitVec.ofNat 64 (r1rawf y3) ∧ S'.regs 3 = BitVec.ofNat 64 (2 * y3) ∧
  S'.regs 2 = S'.regs 0 ||| S'.regs 3 ∧
  S'.regs 1 = BitVec.ofNat 64 (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) + 192#64 ∧
  S'.regs 7 = BitVec.ofNat 64 y2 ∧ S'.regs 8 = BitVec.ofNat 64 y1 ∧ S'.regs 9 = BitVec.ofNat 64 y0 ∧
  y2 = S'.mem.readLE ((s.regs 4).toNat - 528) 8 ∧ y1 = S'.mem.readLE ((s.regs 4).toNat - 536) 8 ∧
  y0 = S'.mem.readLE ((s.regs 4).toNat - 544) 8 ∧
  S'.mem.readLE ((s.regs 4).toNat - 24) 8 = y3 ∧ S'.mem.readLE ((s.regs 4).toNat - 32) 8 = y2 ∧
  S'.mem.readLE ((s.regs 4).toNat - 40) 8 = y1 ∧ S'.mem.readLE ((s.regs 4).toNat - 48) 8 = y0 ∧
  RecRegs s S' ∧ RecMem s S'.mem y3 ∧ 2 ^ 63 ≤ y3 ∧ y3 < 2 ^ 64

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem seg1 (s S : State) (hpc : S.rip = BitVec.ofNat 64 (recEntry + 0xe7)) (hs : RecPre s) (hq : RecQ0 s S) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x14c)) S (RecQ1 s) := by
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, hx15, ⟨hmw, hm⟩, hdm, hdg⟩ := hs
  obtain ⟨y3, hr0, hr6, hregs, hmem, h63, hlt⟩ := hq
  obtain ⟨hr4, hr5, hr14, hx⟩ := hregs
  have hfr := hmem.2.2.2
  simp only [regSP] at hacc hlow hnw hsp
  have hacc' : S.mem.accessible ((s.regs 4).toNat - 576) (576 + 48) true = true := by
    rw [hfr.accessible]; exact hacc
  have hsp4 : (S.regs 4).toNat = (s.regs 4).toNat - 568 := by
    rw [hr4]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  janus64_run [Util.readLE_32, hr0, hr6, hsp4]
  unfold RecQ1
  have hmem' : RecMem s ((((S.mem.writeLE ((s.regs 4).toNat - 24) 8 y3).writeLE ((s.regs 4).toNat - 32) 8
      (S.mem.readLE ((s.regs 4).toNat - 528) 8)).writeLE ((s.regs 4).toNat - 40) 8
      (S.mem.readLE ((s.regs 4).toNat - 536) 8)).writeLE ((s.regs 4).toNat - 48) 8
      (S.mem.readLE ((s.regs 4).toNat - 544) 8)) y3 := by
    refine (((hmem.write _ 8 _ hlow (by omega) (by omega) (by omega) (by omega)).write _ 8 _ hlow (by omega) (by omega) (by omega) (by omega)).write _ 8 _ hlow (by omega) (by omega) (by omega) (by omega)).write _ 8 _ hlow (by omega) (by omega) (by omega) (by omega)
  refine ⟨y3, S.mem.readLE ((s.regs 4).toNat - 528) 8, S.mem.readLE ((s.regs 4).toNat - 536) 8,
    S.mem.readLE ((s.regs 4).toNat - 544) 8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_⟩, hmem', h63, hlt⟩
  · simp [setRegF, hr6]
  · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]
    rw [rax_eq y3 h63 hlt, add_self_ofNat]
    rfl
  · simp [setRegF]; exact add_self_ofNat y3
  · simp only [setRegF, ↓reduceIte, Nat.reduceEqDiff]
    exact BitVec.or_comm _ _
  · simp [setRegF]; rw [hmem.2.1.1]
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
  · simp [setRegF, hr4]
  · simp [setRegF, hr5]
  · simp [setRegF, hr14]
  · simp [hx]

/-- segments 0 and 1 composed: entry .. `recEntry + 0x14c` -/
theorem seg01 (s : State) (hpc : s.rip = BitVec.ofNat 64 recEntry) (hs : RecPre s)
    (hm3 : s.mem.readLE ((s.regs 0).toNat + 24) 8 ≠ 0)
    (hnp : ¬ ((BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) - 1#64 &&&
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) |||
          (BitVec.ofNat 64 (s.mem.readLE (s.regs 0).toNat 8) |||
              BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 8) 8) |||
            BitVec.ofNat 64 (s.mem.readLE ((s.regs 0).toNat + 16) 8))).toNat = 0)) :
    ReachesRet Fv256.RecipProg.program (BitVec.ofNat 64 (recEntry + 0x14c)) s (RecQ1 s) :=
  Fv256.SegCompose.seg_trans (seg0 s hpc hs hm3 hnp) (fun S' hpc' hq => seg1 s S' hpc' hs hq)

end Fv256.Amd64.RecipSeg
