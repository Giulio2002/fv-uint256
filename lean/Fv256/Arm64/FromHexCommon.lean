import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.Arm64.SetFromHexLoops

/-!
# Shared by `FromHex` and `MustFromHex` (arm64)

The `fromHex` callee summary for an allocated receiver, and the composition of the memory frames of the
`runtime.newobject` call and the `fromHex` call.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Fv256.C Fv256.Arm64.SetFromHexLoops

namespace Fv256.Arm64.FromHexCommon

/-- `fromHex_sum` for an allocated receiver: `z` is whatever `X0` holds at the call; the postcondition is written out
(a callee summary's postcondition must be an explicit conjunction for the symbolic executor to unpack it). -/
theorem fromHex_summary (impl : List Segment) (hp len : BitVec 64) :
    Summary (Extracted.program.link impl) fh (fun s => FromHexPre (s.regs 0) hp len s)
      (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
        s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧
        MemFrame s.mem s'.mem [((s.regs 0).toNat, (s.regs 0).toNat + 32), (s.sp.toNat + 16, s.sp.toNat + 24),
          (s.sp.toNat - 24, s.sp.toNat - 8)] ∧
        (∀ v, parseHex (bytesAt s.mem hp.toNat) len.toNat = .ok v →
          s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ val256 s'.mem (s.regs 0).toNat = v) ∧
        (∀ e, parseHex (bytesAt s.mem hp.toNat) len.toNat = .error e →
          s'.regs 0 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e) 8) ∧
          s'.regs 1 = BitVec.ofNat 64 (s.mem.readLE (errAddrOf e + 8) 8))) :=
  fun s hpc hpre => fromHex_sum impl (s.regs 0) hp len s hpc hpre

set_option maxRecDepth 10000 in
theorem frame_comp (m c w m' : Memory) (rt : List (Nat × Nat)) (sp wa v : Nat) (hsp : 4144 ≤ sp)
    (hin : InRanges wa 32 rt) (hA : MemFrame m c [(sp - 4144, sp + 24)])
    (hfr : MemFrame c w (rt ++ [(sp - 48 - 4096, sp - 48 - 8), (sp - 48 + 8, sp - 48 + 8 + 8)]))
    (hfr2 : MemFrame (w.writeLE (sp - 16) 8 v) m'
      [(wa, wa + 32), (sp - 48 + 16, sp - 48 + 24), (sp - 48 - 24, sp - 48 - 8)]) :
    MemFrame m m' (rt ++ [(sp - 4144, sp + 24)]) := by
  have hB : MemFrame m w (rt ++ [(sp - 4144, sp + 24)]) := by
    refine hA.trans hfr ?_
    intro a n h
    rw [outside_append] at h
    obtain ⟨h1, h2⟩ := h
    simp only [outside_cons, outside_nil] at h2
    refine ⟨?_, ?_⟩
    · simp only [outside_cons, outside_nil]; exact ⟨h2.1, trivial⟩
    · rw [outside_append]
      refine ⟨h1, ?_⟩
      simp only [outside_cons, outside_nil]
      obtain ⟨h3, -⟩ := h2
      refine ⟨?_, ?_, trivial⟩ <;> omega
  have hC : MemFrame m (w.writeLE (sp - 16) 8 v) (rt ++ [(sp - 4144, sp + 24)]) :=
    hB.writeLE v (r := (sp - 4144, sp + 24)) (by simp) (by dsimp only; omega) (by dsimp only; omega)
  refine hC.trans hfr2 ?_
  intro a n h
  refine ⟨h, ?_⟩
  rw [outside_append] at h
  obtain ⟨h1, h2⟩ := h
  simp only [outside_cons, outside_nil] at h2 ⊢
  have h3 := InRanges.disjoint hin h1
  obtain ⟨h4, -⟩ := h2
  refine ⟨?_, ?_, ?_, trivial⟩ <;> omega

end Fv256.Arm64.FromHexCommon
