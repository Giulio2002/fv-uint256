import Fv256.ChainProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.KnuthMathB
import Fv256.UdivMathB
import Fv256.UdivremMath
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremH
import Fv256.Amd64.UdivremI
import Fv256.Amd64.UdivremJ

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA Fv256.Amd64.UdivremH Fv256.Amd64.UdivremI

namespace Fv256.Amd64.UdivremK

theorem ofNat_toNat64 (x : W64) : BitVec.ofNat 64 x.toNat = x := by simp

set_option maxHeartbeats 32000000 in
theorem udivrem_summary_L {L : Nat} (hL : 4 ≤ L ∧ L ≤ 8) :
    Summary Fv256.ChainProg.program ku
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x150 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0xf8 ∧ StackWritable s 0x148 0x48 ∧ s.xmm 15 = 0 ∧
        (s.regs 6).toNat = L ∧ (s.regs 3).toNat = L ∧
        Buffer s (s.regs 0) (8 * L) true ∧ Buffer s (s.regs 7) (8 * L) false ∧ Buffer s (s.regs 9) 32 false ∧
        ((s.regs 0).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 7).toNat) ∧
        ((s.regs 9).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 9).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 14).toNat + 16) ∧
        Fv256.B.wv s.mem (s.regs 9).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧
        ((s.regs 10).toNat ≠ 0 → Buffer s (s.regs 10) 32 true ∧ Fv256.B.wv s.mem (s.regs 10).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 8 * L ≤ (s.regs 10).toNat ∨ (s.regs 10).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * L ≤ (s.regs 10).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 10).toNat)))
      (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory) (kr : Nat → W64),
        s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i,
                      rip := retAddrOf s, flags := fl', xmm := fun i => if i = 15 then s.xmm 15 else X' i, mem := M', kreg := kr } ∧
        Fv256.B.wv M' (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 7).toNat L / Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        ((s.regs 10).toNat ≠ 0 → Fv256.B.wv M' (s.regs 10).toNat 4 =
          Fv256.B.wv s.mem (s.regs 7).toNat L % Fv256.B.wv s.mem (s.regs 9).toNat 4) ∧
        ((s.regs 10).toNat = 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)]) ∧
        ((s.regs 10).toNat ≠ 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L), ((s.regs 10).toNat, (s.regs 10).toNat + 32),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)])) := by
  intro s hpc ⟨⟨hra1, hra2⟩, hsp0, hg, hw, hx15, h6, h3, ⟨hqb, hqa⟩, ⟨hub, hua⟩, ⟨hdb, hda⟩, hqs, hus, hds, hgd, hD0, hq0, hrem⟩
  have hrip : { s with regs := s.regs, rip := BitVec.ofNat 64 ku, flags := s.flags, mem := s.mem } = s := by rw [← hpc]
  obtain ⟨hlow, hnw, hacc⟩ := hw
  simp only [regSP] at hlow hnw hacc
  have hg3 : s.mem.readLE ((s.regs 14).toNat + 16) 8 < (s.regs 4).toNat - 0xf8 := by
    have := hg.below
    simp only [stackguard0, stackguard0Offset, regSP, regG] at this
    omega
  have hg1 : (s.regs 14).toNat + 24 ≤ 2 ^ 48 := by
    have := hg.noWrap
    simp only [stackguard0Offset, regG] at this
    omega
  have hg2 : s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true := by
    have := hg.readable
    simpa [stackguard0Offset, regG] using this
  have hMs : s.mem.accessible ((s.regs 4).toNat - 0x148) 0x190 true = true := by simpa using hacc
  have e4 := (ofNat_toNat64 (s.regs 4)).symm
  have e9 := (ofNat_toNat64 (s.regs 9)).symm
  have e0 := (ofNat_toNat64 (s.regs 0)).symm
  have e3 := (ofNat_toNat64 (s.regs 3)).symm
  have e1 := (ofNat_toNat64 (s.regs 1)).symm
  have e7 := (ofNat_toNat64 (s.regs 7)).symm
  have e10 := (ofNat_toNat64 (s.regs 10)).symm
  have e6 : s.regs 6 = BitVec.ofNat 64 L := by rw [← h6]; exact (ofNat_toNat64 (s.regs 6)).symm
  have hqp := (s.regs 0).isLt
  have hql := (s.regs 3).isLt
  have hqc := (s.regs 1).isLt
  have hup := (s.regs 7).isLt
  have hremp := (s.regs 10).isLt
  have h1 := Fv256.Amd64.UdivremH.front hL s s.regs s.flags s.mem (s.regs 4).toNat (s.regs 9).toNat (s.regs 0).toNat (s.regs 1).toNat
    (s.regs 3).toNat (s.regs 7).toNat (s.regs 10).toNat hx15 e4 e9 e0 e3 e1 e7 e10 e6 hqp hql hqc hup hremp hsp0 (by omega) hMs
    hdb hda hds hub hua hus hg1 hg2 (by simpa using hg3) hgd hD0
  rw [hrip] at h1
  refine Fv256.B.reachesRet_trans64 h1 ?_
  intro S1 _ ⟨R1, fl1, M1, kr1, n, ulen, sh, hS1, F, r5, r14⟩
  subst hS1
  have hfr := F.frame
  have hR14 : R1 14 = s.regs 14 := r14
  have hrem' : (s.regs 10).toNat ≠ 0 → (s.regs 10).toNat + 32 ≤ 2 ^ 48 ∧ s.mem.accessible (s.regs 10).toNat 32 true = true ∧
      Fv256.B.wv s.mem (s.regs 10).toNat 4 = 0 := fun h => by
    obtain ⟨⟨a, b⟩, c, _, _, _⟩ := hrem h
    exact ⟨a, b, c⟩
  have fin : ∀ S', UPost L { s with kreg := kr1 } s.mem (s.regs 4).toNat (s.regs 9).toNat (s.regs 0).toNat (s.regs 7).toNat (s.regs 10).toNat
      (s.mem.readLE (s.regs 4).toNat 8) (s.regs 5).toNat (s.regs 14) S' → (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory) (kr : Nat → W64),
        s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i,
                      rip := retAddrOf s, flags := fl', xmm := fun i => if i = 15 then s.xmm 15 else X' i, mem := M', kreg := kr } ∧
        Fv256.B.wv M' (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 7).toNat L / Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        ((s.regs 10).toNat ≠ 0 → Fv256.B.wv M' (s.regs 10).toNat 4 =
          Fv256.B.wv s.mem (s.regs 7).toNat L % Fv256.B.wv s.mem (s.regs 9).toNat 4) ∧
        ((s.regs 10).toNat = 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)]) ∧
        ((s.regs 10).toNat ≠ 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L), ((s.regs 10).toNat, (s.regs 10).toNat + 32),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)])) s S' := by
    rintro S' ⟨R', fl', X', M', hS, h4, h5, h14, hx, hq, hr, hf⟩
    have e4 : R' 4 = s.regs 4 + 8 := by
      rw [h4]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]
    have e5 : R' 5 = s.regs 5 := by rw [h5]; exact ofNat_toNat64 _
    have hRf : (fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i) = R' := by
      funext i
      by_cases i4 : i = 4
      · subst i4; simp [e4]
      · by_cases i5 : i = 5
        · subst i5; simp [e5]
        · by_cases i14 : i = 14
          · subst i14; simp [h14]
          · simp [i4, i5, i14]
    have hXf : (fun i => if i = 15 then s.xmm 15 else X' i) = X' := by
      funext i
      by_cases i15 : i = 15
      · subst i15; simp [hx]
      · simp [i15]
    refine ⟨R', fl', X', M', kr1, ?_, hq, hr, hf⟩
    rw [hRf, hXf, hS]
    rfl
  rcases Nat.lt_or_ge ulen n with hlt | hge
  · exact Fv256.B.reachesRet_mono64 (Fv256.Amd64.UdivremI.caseL hL { s with kreg := kr1 } R1 fl1 M1 s.mem (s.regs 4).toNat (s.regs 9).toNat (s.regs 0).toNat
      (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat (s.regs 10).toNat n ulen sh (s.regs 5).toNat (s.mem.readLE (s.regs 4).toNat 8)
      F hlt (s.regs 14) hR14 hsp0 (by omega) hMs hub hua hus hdb hds hqb hq0 hqs hremp hrem'
      (fun h => (hrem h).2.2.1) (fun h => (hrem h).2.2.2.1) (fun h => (hrem h).2.2.2.2) hra2 hx15) fin
  · rcases Nat.eq_or_lt_of_le F.hn with h1n | h2n
    · exact Fv256.B.reachesRet_mono64 (Fv256.Amd64.UdivremJ.caseOne hL { s with kreg := kr1 } R1 fl1 M1 s.mem (s.regs 4).toNat (s.regs 9).toNat (s.regs 0).toNat
        (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat (s.regs 10).toNat n ulen sh (s.regs 5).toNat (s.mem.readLE (s.regs 4).toNat 8)
        F h1n.symm hge (s.regs 14) hR14 h3 hsp0 (by omega) hMs hub hua hus hdb hds hqb hqa hq0 hqs hremp hrem'
        (fun h => (hrem h).2.2.1) (fun h => (hrem h).2.2.2.1) (fun h => (hrem h).2.2.2.2) hra2 hx15
        (by rw [hR14]; exact hg1) (by rw [hR14]; exact hg2) (by rw [hR14]; exact hg3) (by rw [hR14]; exact hgd)) fin
    · exact Fv256.B.reachesRet_mono64 (Fv256.Amd64.UdivremI.caseK hL { s with kreg := kr1 } R1 fl1 M1 s.mem (s.regs 4).toNat (s.regs 9).toNat (s.regs 0).toNat
        (s.regs 1).toNat (s.regs 3).toNat (s.regs 7).toNat (s.regs 10).toNat n ulen sh (s.regs 5).toNat (s.mem.readLE (s.regs 4).toNat 8)
        F h2n hge (s.regs 14) hR14 h3 hsp0 (by omega) hMs hub hua hus hdb hds hqb hqa hq0 hqs hremp hrem'
        (fun h => (hrem h).2.2.1) (fun h => (hrem h).2.2.2.1) (fun h => (hrem h).2.2.2.2) hra2 hx15
        (by rw [hR14]; exact hg1) (by rw [hR14]; exact hg2) (by rw [hR14]; exact hg3) (by rw [hR14]; exact hgd)) fin

/-- the `L = 4` instance (unchanged statement; used by the 4-limb `Div`/`Mod`/`DivMod` wrappers) -/
theorem udivrem_summary :
    Summary Fv256.ChainProg.program ku
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x150 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0xf8 ∧ StackWritable s 0x148 0x48 ∧ s.xmm 15 = 0 ∧
        (s.regs 6).toNat = 4 ∧ (s.regs 3).toNat = 4 ∧
        Buffer s (s.regs 0) 32 true ∧ Buffer s (s.regs 7) 32 false ∧ Buffer s (s.regs 9) 32 false ∧
        ((s.regs 0).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 7).toNat) ∧
        ((s.regs 9).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 9).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 14).toNat + 16) ∧
        Fv256.B.wv s.mem (s.regs 9).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat 4 = 0 ∧
        ((s.regs 10).toNat ≠ 0 → Buffer s (s.regs 10) 32 true ∧ Fv256.B.wv s.mem (s.regs 10).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 32 ≤ (s.regs 10).toNat ∨ (s.regs 10).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 32 ≤ (s.regs 10).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 10).toNat)))
      (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory) (kr : Nat → W64),
        s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i,
                      rip := retAddrOf s, flags := fl', xmm := fun i => if i = 15 then s.xmm 15 else X' i, mem := M', kreg := kr } ∧
        Fv256.B.wv M' (s.regs 0).toNat 4 = Fv256.B.wv s.mem (s.regs 7).toNat 4 / Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        ((s.regs 10).toNat ≠ 0 → Fv256.B.wv M' (s.regs 10).toNat 4 =
          Fv256.B.wv s.mem (s.regs 7).toNat 4 % Fv256.B.wv s.mem (s.regs 9).toNat 4) ∧
        ((s.regs 10).toNat = 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 32),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)]) ∧
        ((s.regs 10).toNat ≠ 0 → MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 32), ((s.regs 10).toNat, (s.regs 10).toNat + 32),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)])) := fun s hpc h => udivrem_summary_L (L := 4) (by omega) s hpc h

end Fv256.Amd64.UdivremK
