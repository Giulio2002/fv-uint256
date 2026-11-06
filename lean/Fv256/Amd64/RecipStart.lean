import Fv256.Amd64.RecipLive

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.RecipSeg

/-- the generated chain starts at `recEntry + 0x14c` with these variable values (from `RecQ1`) -/
def Start14c (s : State) (y3 : Nat) (x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 : Nat) : Prop :=
  x14crax = r1rawf y3 % 18446744073709551616 ∧ x14crbx = 2 * y3 % 18446744073709551616 ∧
  x14crdx = (x14crax ||| x14crbx) ∧ x14crsi = y3 ∧ x14cm220 = y3 ∧ x14crdi = x14cm218 ∧ x14cr8 = x14cm210 ∧ x14cr9 = x14cm208 ∧
  x14crcx = (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) + 192) % 18446744073709551616 ∧
  x14cm208 + 18446744073709551616 * x14cm210 + 18446744073709551616 ^ 2 * x14cm218 + 18446744073709551616 ^ 3 * y3 =
    Fv256.Spec.lsh (s.mem.readLE (s.regs 0).toNat 32) (Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8)) ∧
  2 ^ 63 ≤ y3 ∧ y3 < 2 ^ 64

theorem start14c (s S : State) (hlow : 576 ≤ (s.regs 4).toNat) (hq : RecQ1 s S) : ∃ y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220,
    L14c s S x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 ∧
    Start14c s y3 x14crax x14crcx x14crdx x14crbx x14crsi x14crdi x14cr8 x14cr9 x14cm208 x14cm210 x14cm218 x14cm220 ∧
    RecRegs s S ∧ RecMem s S.mem y3 := by
  obtain ⟨y3, y2, y1, y0, hr6, hr0, hr3, hr2, hr1, hr7, hr8, hr9, hy2, hy1, hy0, hs24, hs32, hs40, hs48, hregs, hmem, h63, hlt⟩ := hq
  have hM := Util.readLE8_lt
  have hb2 : y2 < 2 ^ 64 := by rw [hy2]; exact Util.readLE8_lt _ _
  have hb1 : y1 < 2 ^ 64 := by rw [hy1]; exact Util.readLE8_lt _ _
  have hb0 : y0 < 2 ^ 64 := by rw [hy0]; exact Util.readLE8_lt _ _
  have hax : r1rawf y3 % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have hbx : 2 * y3 % 18446744073709551616 < 18446744073709551616 := Nat.mod_lt _ (by decide)
  have hor : (r1rawf y3 % 18446744073709551616 ||| 2 * y3 % 18446744073709551616) < 18446744073709551616 :=
    Nat.or_lt_two_pow (n := 64) hax hbx
  have hcx : (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) + 192) % 18446744073709551616 < 18446744073709551616 :=
    Nat.mod_lt _ (by decide)
  refine ⟨y3, r1rawf y3 % 18446744073709551616, (63 - Janus.Arm64.clzNat 64 (s.mem.readLE ((s.regs 0).toNat + 24) 8) + 192) % 18446744073709551616,
    (r1rawf y3 % 18446744073709551616 ||| 2 * y3 % 18446744073709551616), 2 * y3 % 18446744073709551616, y3, y2, y1, y0, y0, y1, y2, y3, ?_, ?_, hregs, hmem⟩
  · unfold L14c
    refine ⟨?_, hax, ?_, hcx, ?_, hor, ?_, hbx, hr6, hlt, hr7, hb2, hr8, hb1, hr9, hb0, hs48, hb0, hs40, hb1, hs32, hb2, hs24, hlt⟩
    · rw [hr0, ofNat_mod64]
    · rw [hr1, ofNat_mod64, BitVec.ofNat_add]
    · rw [hr2, hr0, hr3]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt hor]
    · rw [hr3, ofNat_mod64]
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, h63, hlt⟩
    have h32 := hmem.2.2.1
    rw [Util.readLE_32] at h32
    have e1 : (s.regs 4).toNat - 544 + 8 = (s.regs 4).toNat - 536 := by omega
    have e2 : (s.regs 4).toNat - 544 + 16 = (s.regs 4).toNat - 528 := by omega
    have e3 : (s.regs 4).toNat - 544 + 24 = (s.regs 4).toNat - 520 := by omega
    rw [e1, e2, e3, ← hy0, ← hy1, ← hy2, ← hmem.1] at h32
    rw [← h32]

end Fv256.Amd64.RecipSeg
