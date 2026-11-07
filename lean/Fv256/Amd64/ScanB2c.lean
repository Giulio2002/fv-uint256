import Extracted
import Fv256.Amd64.ScanSpec
import Fv256.Amd64.ScanCfg
import Fv256.Amd64.ScanBSb

/-!
# `Scan` (amd64), `[]byte` source: the precondition of the `slicebytetostring` live contract, from explicit facts about an abstract entry state

Everything is stated about `S0.mem` (no store chain), so the unfolding of `RtLivePre64` is cheap.
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Amd64.ScanCfg

namespace Fv256.Amd64.ScanB

theorem argw3 (S0 : State) (a0 a1 a2 : Nat) (h0 : (S0.regs 0).toNat = a0) (h1 : (S0.regs 3).toNat = a1) (h2 : (S0.regs 1).toNat = a2) :
    argWords64 S0 3 = [a0, a1, a2] := by
  unfold argWords64
  simp [wordsFrom, h0, h1, h2]

set_option maxRecDepth 100000 in
theorem sb_pre (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (S0 : State) (buf ptr n : Nat)
    (hargs : argWords64 S0 3 = [buf, ptr, n])
    (c1 : S0.mem.readLE (S0.regs 4).toNat 8 < 2 ^ 47) (c2 : (S0.regs 4).toNat % 8 = 0) (c3 : 4096 ≤ (S0.regs 4).toNat)
    (c4 : (S0.regs 4).toNat + 8 + 8 * 3 ≤ 2 ^ 48)
    (c5 : S0.mem.accessible ((S0.regs 4).toNat - 4096) (4096 + 8 + 8 * 3) true = true)
    (d1 : BufOK S0.mem buf 32) (d2 : StrIn S0.mem ptr n) (d3 : buf ≠ 0 → Spec.Disjoint ptr n buf 32)
    (e1 : Outside ptr n [((S0.regs 4).toNat - 4096, (S0.regs 4).toNat), ((S0.regs 4).toNat + 8, (S0.regs 4).toNat + 8 + 8 * 3)])
    (g1 : (S0.regs 14).toNat + 24 ≤ 2 ^ 48) (g2 : S0.mem.accessible ((S0.regs 14).toNat + 16) 8 false = true)
    (g3 : S0.mem.readLE ((S0.regs 14).toNat + 16) 8 + 4096 < (S0.regs 4).toNat)
    (g4 : Outside ((S0.regs 14).toNat + 16) 8 [((S0.regs 4).toNat - 4096, (S0.regs 4).toNat), ((S0.regs 4).toNat + 8, (S0.regs 4).toNat + 8 + 8 * 3)])
    (l1 : R.ok sbAddr [buf, ptr, n]) (l2 : R.inv b L (S0.regs 14).toNat (view R.rt L S0.mem)) (l3 : roundupsize n true ≤ b)
    (l4 : LiveSep L ([((S0.regs 4).toNat - 4096, (S0.regs 4).toNat), ((S0.regs 4).toNat + 8, (S0.regs 4).toNat + 8 + 8 * 3)] ++
        [((S0.regs 4).toNat, (S0.regs 4).toNat + 8)]))
    (l5 : LiveSep ([((S0.regs 4).toNat - 4096, (S0.regs 4).toNat), ((S0.regs 4).toNat + 8, (S0.regs 4).toNat + 8 + 8 * 3)] ++
        [((S0.regs 4).toNat, (S0.regs 4).toNat + 8)]) R.rt) :
    RtLivePre64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive sbAddr L b S0 := by
  unfold RtLivePre64
  simp only [slicebytetostringSpec, slicebytetostringLive, CallOK64, StackRoom64, GuardOK64, LiveAt, calleeStack64, liveWin64, hargs]
  simp only [List.getD_cons_zero, List.getD_cons_succ, arg]
  refine ⟨⟨c1, c2, c3, c4, c5⟩, ⟨d1, d2, d3⟩, ?_, trivial, ⟨⟨g1, g2, g3⟩, g4⟩, l1, l2, l3, l4, l5⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact e1

set_option maxRecDepth 100000 in
/-- the postcondition of the live contract of `slicebytetostring`, as `SbPost` (the facts about the entry memory `S0.mem` of the call, with the string unchanged between `S0.mem` and `s.mem`) -/
theorem sb_post (R : RtInv) (L : List (Nat × Nat)) (b : Nat) (s S0 s' : State) (pI nI : BitVec 64) (buf : Nat)
    (hargs : argWords64 S0 3 = [buf, pI.toNat, nI.toNat]) (hbuf : buf = (s.regs 4).toNat - 40)
    (hsp0 : (S0.regs 4).toNat = (s.regs 4).toNat - 72)
    (hstr : strBytes S0.mem pI.toNat nI.toNat = strBytes s.mem pI.toNat nI.toNat) (hreg0 : S0.mem.regions = s.mem.regions) (hr14 : S0.regs 14 = s.regs 14)
    (hq : RtLivePost64 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive L b S0 s') :
    ∃ (r0 r1 r2 : W64) (junk : Nat → W64) (f : Flags) (x yh : Nat → BitVec 128) (m : Janus.Arm64.Memory)
      (zh : Nat → BitVec 256) (kr : Nat → W64),
      s' = retState64 S0 junk [r0, r1, r2] f x yh m zh kr ∧
      Fv256.Amd64.ScanBSb.SbPost R stAddr b L s pI nI r0 r1 S0.mem m buf := by
  unfold RtLivePost64 at hq
  simp only [slicebytetostringSpec, slicebytetostringLive, calleeStack64, liveWin64, hargs, arg,
    List.getD_cons_zero, List.getD_cons_succ] at hq
  obtain ⟨r0, r1, r2, junk, f, x, yh, m, zh, kr, hs', hMF, ⟨hSO, hSA⟩, hLF, hFr, hLA, hInv⟩ := hq
  have hsl : (strBytes s.mem pI.toNat nI.toNat).length = nI.toNat := by simp
  have hsl0 : (strBytes S0.mem pI.toNat nI.toNat).length = nI.toNat := by simp
  have hMFc := hMF
  obtain ⟨hl, hb48, hacc, hbs⟩ := hSO
  refine ⟨r0, r1, r2, junk, f, x, yh, m, zh, kr, hs', ?_, ⟨⟨?_, hb48, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · have hMF' := hMF
    simp only [rtIf_true, bufWrites, hsp0, Nat.reduceMul] at hMF'
    exact hMF'
  · rw [hsl]; omega
  · intro h
    rw [← Janus.Arm64.Memory.accessible_congr hreg0, ← hMFc.accessible]; exact hacc h
  · rw [← hstr]; exact hbs
  · exact hSA
  · simp only [bufWrites] at hLF; exact hLF
  · exact hFr
  · simp only [liveAdds, List.getD_cons_zero, range0, hr14] at hInv
    exact hInv

end Fv256.Amd64.ScanB
